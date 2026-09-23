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
  prebuilt `Benchmark` heap, which already bundles `HOL-Number_Theory`,
  `HOL-Algebra`, `HOL-Combinatorics`, `HOL-Cardinals`,
  `HOL-Computational_Algebra`, `HOL-Decision_Procs`, `HOL-Real_Asymp`, and
  `HOL-Eisbach` as sibling sessions — `imports` any of those directly, no
  separate build wait. This is the mode with the actual safety net: it
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
  `Benchmark` siblings listed above).
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
