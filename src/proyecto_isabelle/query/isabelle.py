import os
import re
from pathlib import Path
from typing import Literal, Optional
from uuid import uuid4

import httpx
from pydantic import BaseModel, Field

from proyecto_isabelle.parse import thy

DEFAULT_TIMEOUT = 60
DEFAULT_PARENT_SESSION = "Benchmark"

# Sibling library sessions bundled into the DeepIsaHOL image's `Benchmark` heap.
# They are declared in the generated ROOT so a submitted theory can `imports` any
# of them without triggering an on-the-fly session build.
BENCHMARK_SIBLING_SESSIONS = (
    "HOL-Number_Theory",
    "HOL-Algebra",
    "HOL-Combinatorics",
    "HOL-Cardinals",
    "HOL-Computational_Algebra",
    "HOL-Decision_Procs",
    "HOL-Real_Asymp",
    "HOL-Eisbach",
)

Mode = Literal["build", "verify"]

_THEORY_HEADER = re.compile(r"\btheory\s+([A-Za-z][\w']*)")
_UNSOUND_COMMAND = re.compile(r"\b(sorry|oops)\b")
_ISABELLE_COMMENT = re.compile(r"\(\*.*?\*\)", re.DOTALL)
# `axiomatization`/`axioms` let a theory assert its own goal as a new axiom
# and then "prove" it by citing that axiom -- a green build with no sorry/
# oops that still proves nothing derived from the actual libraries.
_AXIOM_COMMAND = re.compile(r"\baxiomatization\b|\baxioms\b")
# A real `lemma`/`theorem` command: the keyword followed by either a name
# and colon (`lemma foo:`) or an anonymous statement (`lemma "..."`). Without
# this, a comment-only theory (e.g. one that just argues the goal is false)
# trivially "builds" with nothing to fail on, and would otherwise count as
# verified.
_STATEMENT_COMMAND = re.compile(r"\b(?:lemma|theorem)\b\s*(?:\S+\s*:|\")")

# Prefix of the error `_run_build` appends when `incomplete` is non-empty --
# shared with `analysis.integrity` so it can recognize a `benchmark` row this
# project retroactively re-flagged as gamed (same error text, since the
# retroactive fix script reused this exact message) without re-deriving
# "gamed" from content alone, which would also match unrelated pre-existing
# rows that happen to share a reason (e.g. an old `check_in_isabelle`-probe
# with no statement) without ever having been corrected.
INCOMPLETE_PROOF_ERROR_PREFIX = (
    "Build succeeded but the proof doesn't count as verified"
)


def _resolve_api_url(api_url: str | None) -> str:
    if api_url is None:
        api_url = os.getenv("ISABELLE_API_URL", "http://localhost:8001")
    if "://" not in api_url:
        # Render's `fromService: ... property: hostport` resolves to a bare
        # "host:port" with no scheme; the private network is plain HTTP.
        api_url = f"http://{api_url}"
    return api_url


class IsabelleRequest(BaseModel):
    """Payload for the DeepIsaHOL ``/verify`` endpoint (REPL, fast path)."""

    thy_content: str = Field(
        ..., description="The complete content of the .thy file to verify"
    )
    logic: str = Field(
        default="HOL", description="The Isabelle logic to use (e.g., HOL, HOL-Analysis)"
    )
    timeout_seconds: int = Field(
        default=300,
        ge=1,
        le=3600,
        description="Timeout in seconds for the verification",
    )


class IsabelleResponse(BaseModel):
    """Uniform validation result, whichever endpoint produced it."""

    success: bool = Field(
        ..., description="Whether the API call itself completed successfully"
    )
    verified: bool = Field(..., description="Whether the proof is complete and correct")
    errors: list[str] = Field(
        default_factory=list,
        description="Human-readable error messages if validation failed",
    )
    state: Optional[str] = Field(
        default=None,
        description="Final Isabelle state after verification (verify mode only)",
    )
    message: str = Field(..., description="Human-readable message about the result")

    # --- additive fields: populated in build mode, inert in verify mode ---
    mode: Mode = Field(
        default="verify", description="Which validation path produced this result"
    )
    build_log: Optional[str] = Field(
        default=None, description="Full `isabelle build` output (build mode only)"
    )
    errors_structured: list[dict] = Field(
        default_factory=list,
        description="Raw {theory, line, message} errors (build mode only)",
    )


def _verify_server_is_running(api_url: str | None = None) -> None:
    api_url = _resolve_api_url(api_url)
    with httpx.Client(timeout=DEFAULT_TIMEOUT) as client:
        try:
            resp = client.get(f"{api_url.rstrip('/')}/health")
        except (ConnectionError, httpx.ConnectError) as e:
            raise RuntimeError(
                "Couldn't connect to the DeepIsaHOL server. Did you remember "
                "to run `docker compose up` or to start the DeepIsaHOL server?"
            ) from e

        if not (200 <= resp.status_code < 300):
            raise RuntimeError(
                "DeepIsaHOL server is not healthy. Did you remember to run "
                "`docker compose up` or to start the DeepIsaHOL server?"
            )


def _strip_comments(text: str) -> str:
    prev = None
    while prev != text:
        prev = text
        text = _ISABELLE_COMMENT.sub(" ", text)
    return text


def _incomplete_commands(thy_content: str) -> list[str]:
    """Reasons a green build still isn't a real, checked proof: `sorry`/
    `oops` left in, the goal asserted via `axiomatization`/`axioms` instead
    of derived, or no `lemma`/`theorem` statement submitted at all (an empty
    or comment-only theory trivially "builds")."""
    stripped = _strip_comments(thy_content)
    reasons = sorted({m.group(1) for m in _UNSOUND_COMMAND.finditer(stripped)})
    if _AXIOM_COMMAND.search(stripped):
        reasons.append("axiomatization")
    if not _STATEMENT_COMMAND.search(stripped):
        reasons.append("no lemma/theorem statement")
    return reasons


def extract_theory_name(thy_content: str) -> str:
    match = _THEORY_HEADER.search(_strip_comments(thy_content))
    if not match:
        raise ValueError(
            "Submitted content has no `theory <Name>` header; cannot build it."
        )
    return match.group(1)


def _format_build_error(err: dict) -> str:
    where = err.get("theory") or ""
    if where and err.get("line"):
        where = f"{where}:{err['line']}"
    prefix = f"{where}: " if where else ""
    return f"{prefix}{err.get('message', '')}".strip()


def _make_root(session_name: str, parent_session: str, theory_name: str) -> str:
    sessions_block = ""
    if parent_session == DEFAULT_PARENT_SESSION:
        listed = "\n".join(f'    "{s}"' for s in BENCHMARK_SIBLING_SESSIONS)
        sessions_block = f"  sessions\n{listed}\n"
    return (
        f'session {session_name} = "{parent_session}" +\n'
        # `isabelle build` defaults quick_and_dirty=false, which makes `sorry` /
        # `oops` a hard build error ("Cheating requires quick_and_dirty mode!").
        # We allow them through here and gate on them in Python instead
        # (`_incomplete_commands` + the `allow_incomplete` flag), so a skeleton
        # with a `sorry` placeholder still gets its parse/type check.
        f"  options [quick_and_dirty = true]\n"
        f"{sessions_block}"
        f"  theories\n"
        f"    {theory_name}\n"
    )


def query_file(
    path: Path | str,
    api_url: str | None = None,
    *,
    mode: Mode = "build",
    parent_session: str = DEFAULT_PARENT_SESSION,
    allow_incomplete: bool = False,
    timeout_seconds: int = 300,
    build_options: list[str] | None = None,
) -> IsabelleResponse:
    content = thy.load_text(path)
    return query_content(
        content,
        api_url=api_url,
        mode=mode,
        parent_session=parent_session,
        allow_incomplete=allow_incomplete,
        timeout_seconds=timeout_seconds,
        build_options=build_options,
    )


def query_content(
    content: str,
    api_url: str | None = None,
    *,
    mode: Mode = "build",
    parent_session: str = DEFAULT_PARENT_SESSION,
    allow_incomplete: bool = False,
    timeout_seconds: int = 300,
    build_options: list[str] | None = None,
) -> IsabelleResponse:
    """Validate a complete .thy file against the DeepIsaHOL server.

    ``mode="build"`` (default): run ``isabelle build`` against the prebuilt
    ``Benchmark`` heap. Honours ``imports``, returns real error locations, and
    -- unless ``allow_incomplete`` -- reports ``verified=False`` when the proof
    still contains ``sorry``/``oops``. Slower (~20-45s).

    ``mode="verify"``: REPL fast path. Ignores ``imports`` (runs on ``Main``) and
    returns the final proof state. Seconds. Used by the web backend.

    ``build_options`` (build mode only): extra ``isabelle build`` flags, e.g.
    ``["-v"]`` to get command-level output (such as ``find_theorems`` results)
    back in ``build_log`` — see ``DeepIsaHOL``'s ``ALLOWED_BUILD_OPTIONS``.
    """
    api_url = _resolve_api_url(api_url)
    _verify_server_is_running(api_url)
    if mode == "verify":
        return _run_verify(content, api_url, timeout_seconds)
    return _run_build(
        content,
        api_url,
        parent_session,
        allow_incomplete,
        timeout_seconds,
        build_options,
    )


def _run_verify(content: str, api_url: str, timeout_seconds: int) -> IsabelleResponse:
    payload = IsabelleRequest(thy_content=content, timeout_seconds=timeout_seconds)
    with httpx.Client(timeout=timeout_seconds + 30) as client:
        raw_response = client.post(
            f"{api_url.rstrip('/')}/verify",
            json=payload.model_dump(mode="json"),
        )
        raw_response.raise_for_status()

    data = raw_response.json()
    return IsabelleResponse(
        success=bool(data.get("success")),
        verified=bool(data.get("verified")),
        errors=list(data.get("errors") or []),
        state=data.get("state"),
        message=data.get("message", ""),
        mode="verify",
    )


def _run_build(
    content: str,
    api_url: str,
    parent_session: str,
    allow_incomplete: bool,
    timeout_seconds: int,
    build_options: list[str] | None = None,
) -> IsabelleResponse:
    theory_name = extract_theory_name(content)
    session_name = f"Sub_{uuid4().hex[:12]}"
    payload = {
        "session_name": session_name,
        "root_content": _make_root(session_name, parent_session, theory_name),
        "theory_files": {f"{theory_name}.thy": content},
        "timeout_seconds": max(1, min(timeout_seconds, 7200)),
        "options": build_options,
    }
    with httpx.Client(timeout=timeout_seconds + 60) as client:
        raw_response = client.post(f"{api_url.rstrip('/')}/build", json=payload)
        raw_response.raise_for_status()

    data = raw_response.json()
    built = bool(data.get("built"))
    structured = list(data.get("errors") or [])
    errors = [_format_build_error(e) for e in structured]
    build_log = data.get("build_log")

    incomplete = _incomplete_commands(content)
    if not incomplete and build_log and _UNSOUND_COMMAND.search(build_log):
        incomplete = ["sorry"]

    verified = built and (allow_incomplete or not incomplete)
    if built and incomplete and not allow_incomplete:
        errors.append(f"{INCOMPLETE_PROOF_ERROR_PREFIX} ({', '.join(incomplete)}).")
        message = f"Proof incomplete: {', '.join(incomplete)}"
    else:
        message = data.get("message") or (
            "Build succeeded" if built else "Build failed"
        )

    return IsabelleResponse(
        success=bool(data.get("success")),
        verified=verified,
        errors=errors,
        state=None,
        message=message,
        mode="build",
        build_log=build_log,
        errors_structured=structured,
    )
