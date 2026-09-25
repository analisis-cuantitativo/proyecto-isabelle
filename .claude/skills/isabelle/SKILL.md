---
name: isabelle
description: Use when formalizing a mathematical statement in Isabelle/HOL, completing the proof of an existing .thy skeleton, or checking whether a candidate .thy file actually verifies in this project. Wraps proyecto_isabelle.query.isabelle.query_content, which talks to the DeepIsaHOL server — never claim a proof works without having run it through this.
---

# Isabelle proof assistant

Isabelle's type-checker and tactics are the ground truth, not your own
judgment about whether a proof "looks right". Every claim that a proof is
correct must be backed by a `query_content(..., mode="build")` call in this
session that came back with `verified=True`.

## Prerequisites

The DeepIsaHOL server must be running:

```bash
docker compose up   # from the repo root; exposes the API on localhost:8001
```

The client resolves its URL from `ISABELLE_API_URL`, defaulting to
`http://localhost:8001` (see `_resolve_api_url` in
`src/proyecto_isabelle/query/isabelle.py`) — no need to set it unless you're
pointing at something else. If the server isn't reachable, `query_content`
raises a `RuntimeError` telling you to run `docker compose up`; don't work
around that by fabricating a result.

## Check which libraries the server actually has before you start

The `Benchmark` heap's composition is configurable per deployment and
defaults to bare `HOL` — no Analysis, Probability, Algebra, etc. (see
`DEEPISAHOL_PARENT_SESSION` / `DEEPISAHOL_EXTRA_SESSIONS` in the root
`README.md`, "Configurando qué librerías de Isabelle se compilan"). Before
drafting a skeleton, check `GET {api_url}/sessions` (or just read what
`query_content` needs — it calls this for you internally) to see what's
already bundled, rather than assuming any particular library is there.

If the exercise you're about to formalize clearly needs something outside
what's bundled — real analysis (limits, derivatives, integrals) needs
`HOL-Analysis`, probability needs `HOL-Probability`, number theory needs
`HOL-Number_Theory`, abstract algebra needs `HOL-Algebra`, and so on (full
table in the README section above) — don't just try it and let the build
fail on a missing `imports`. Two cases:

- **It's obvious from the statement** (e.g. a problem about continuity
  obviously needs `HOL-Analysis`): say so and propose the specific
  `DEEPISAHOL_EXTRA_SESSIONS`/parent change up front, before spending build
  calls on something that can't possibly resolve.
- **It's ambiguous, or you're about to formalize a whole batch of exercises
  with mixed needs**: ask the user which sessions to include rather than
  guessing — getting this wrong either wastes their time on a rebuild for
  the wrong set, or silently narrows what you can even attempt.

Rebuilding to add a session is a real, potentially expensive Docker build
(seconds for `HOL`-only, up to ~1-2h for the old full Analysis/Probability
set) — this is not something to kick off on your own initiative. Confirm
with the user first, the same as any other slow/resource-heavy action; once
they approve, the change is `docker compose build deepisahol` with the new
build args, then restarting the service. `GET /sessions` reflects the new
composition automatically the moment the rebuilt container is up — no
separate step needed after that.

## Call the existing client, don't hand-roll HTTP

There's already a Python client with unicode normalization, ROOT-file
generation for the `Benchmark` session, and built-in cheat detection — use
it instead of curling `/build`/`/verify` directly:

```bash
uv run python -c "
from proyecto_isabelle.query import isabelle

result = isabelle.query_content(open('path/to/file.thy').read(), mode='build')
print(result.verified, result.errors)
"
```

Or, for a file already on disk, `isabelle.query_file(path)` does the same
thing without reading it yourself first.

## Two modes — prefer `build`

- **`mode="build"` (default).** Runs a real `isabelle build` against the
  prebuilt `Benchmark` heap. *Which* libraries that heap bundles is
  configurable per deployment (`DEEPISAHOL_PARENT_SESSION` /
  `DEEPISAHOL_EXTRA_SESSIONS` at the server's Docker build time — see the
  root `README.md`, "Configurando qué librerías de Isabelle se compilan").
  Don't assume a library is available; check the running server with
  `GET /sessions` (or `proyecto_isabelle.query.isabelle._benchmark_sessions`,
  which the client already calls automatically to know what it can put in a
  generated `sessions` clause). A theory's `imports` only resolves instantly
  if the referenced session is one of those already bundled — anything else
  triggers an on-the-fly build or fails outright. This is the mode with the
  actual safety net: it
  rejects `verified=True` if the content still contains `sorry`/`oops`, uses
  `axiomatization`/`axioms` to assert the goal instead of deriving it, or
  submits no `lemma`/`theorem` statement at all (see `_incomplete_commands`
  in `query/isabelle.py`) — this is exactly the axiomatization cheat the
  project's own benchmark caught a model doing on a group-theory exercise.
  Slower (~20-45s).
- **`mode="verify"`.** A fast REPL path used by the web backend. It ignores
  `imports` (runs against plain `Main` only) and returns the raw final proof
  state — but it does **not** run any of the `sorry`/`oops`/axiomatization
  checks above, since those live only in the build-mode code path. Don't use
  it as your final check; it's for quick, throwaway sanity checks only.

Two flags matter on `mode="build"`:
- `allow_incomplete=False` (default) — this is the real check. A final
  answer must pass this.
- `allow_incomplete=True`, combined with `build_options=["-v"]` — exploration
  mode: `sorry`/`oops` are fine, and the reply's `build_log` includes what
  commands like `find_theorems`/`find_consts` printed (plain `isabelle
  build` doesn't surface that otherwise). Use this to look around a library
  or sanity-check that a skeleton parses before committing to a proof
  strategy — it's what the proof agent's own `query_isabelle` tool does
  internally (see `query/proof_agent.py`).

## Workflow

1. Draft a **skeleton** if none exists: a self-contained `.thy` with the
   statement declared and `sorry` as the only proof step. Check it parses
   and type-checks with `allow_incomplete=True` before writing any tactics.
2. Fill in the proof. After every edit, re-run with
   `mode="build", allow_incomplete=False`. Read `result.errors` (unsolved
   goals, undefined facts/constants, type mismatches, malformed syntax) and
   use them to decide the next tactic — don't guess blind and resubmit
   unchanged.
3. Budget yourself: the project's own agent caps this at 5 build calls and 5
   exploration calls per exercise (`ProofDeps.max_isabelle_checks` /
   `max_isabelle_queries` in `query/proof_agent.py`) — match that unless the
   user asks for more. `isabelle build` is expensive in RAM/CPU
   (`BUILD_MAX_WORKERS` in `DeepIsaHOL/docker/api.py` caps concurrent builds
   at 2 by default for this reason), so don't fire off parallel checks
   against the same server either.
4. Only report a proof as done once `result.verified` is `True` from a
   `mode="build"` call. A submission that was never checked, or was only
   checked with `mode="verify"`, is not done.

## `.thy` conventions

- Self-contained: one theory per file, `imports Main` at minimum, plus only
  the libraries the statement actually needs (`Complex_Main`,
  `"HOL-Analysis.Analysis"`, `"HOL-Probability.Probability"`, or any of the
  `Benchmark` siblings the running server reports at `GET /sessions`). If the
  server was built with the default minimal profile (bare `HOL`, no extras),
  none of those are available — check first rather than assuming.
- Use ASCII notation (`<Rightarrow>`, `<longleftrightarrow>`, `<exists>`,
  `<forall>`, `<and>`, `<or>`, `<noteq>`, `<Longrightarrow>`, ...) instead of
  unicode symbols — the client normalizes common cases
  (`ISABELLE_UNICODE_TO_ASCII` in `DeepIsaHOL/docker/api.py`), but writing
  ASCII directly avoids relying on that.
- Standard tactics first: `auto`, `simp`, `blast`, `induct`; reach for
  heavier automation (`sos`, `approximation`, `real_asymp`, all pulled in
  via the corresponding `HOL-*` sibling) only when the standard ones stall.

## Known failure mode to avoid

Don't "prove" a goal by axiomatizing it and then discharging it via `assms`
— `mode="build"` already rejects this (see `_AXIOM_COMMAND` above), but
don't attempt it in the first place: it wastes a check call and, if you were
ever calling `mode="verify"` instead, it would silently pass.
