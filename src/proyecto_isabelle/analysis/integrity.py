"""Data-integrity checks on `benchmark` itself, not on model performance: is
the recorded ground truth for a run actually internally consistent?

`sync.models.Benchmark` documents the highest-`pass_number` row as a run's
final, independently-reverified answer -- every other module in this package
(`difficulty`, `topics`, `tokens`) takes that at face value. This module
checks whether that's actually always true: a run can have an *earlier* pass
that verified, followed by a *later* (final) pass in the same run that
didn't. Under the standard scoring convention that run counts as unsolved,
even though Isabelle accepted a *pass* somewhere in its trace.

Found by manually diffing a handful of exercises where one model uniquely
solved something every other model failed. The first read of this was that
the losing models had a working proof and then regressed to something worse
-- diffing `thy_content` shows that's only true for some of them. In the
rest, the "verified" earlier pass was never a real proof attempt at all: the
model used `check_in_isabelle` (which requires a complete, sorry/oops-free
theory) to probe the environment instead -- `find_theorems` lookups, `thm`
citations, or a throwaway `lemma test: "1 + 1 = 2" by simp` -- and that
probe happened to build cleanly, which was enough to mark the pass
`verified`. `check_in_isabelle`'s own docstring says not to do this (that's
what `query_isabelle` is for), but models do it anyway, tool availability
notwithstanding: most of these predate `query_isabelle` by days, not hours.
`looks_like_probe` catches this so `classify_by_content` doesn't miscredit
those runs as "the model had a real proof and threw it away."
"""

from __future__ import annotations

import re

import pandas as pd

from proyecto_isabelle.query.isabelle import INCOMPLETE_PROOF_ERROR_PREFIX
from proyecto_isabelle.sync.repository import SupabaseRepository

_NAME_RE = re.compile(r"\b(?:lemma|theorem)\s+([A-Za-z_][A-Za-z0-9_']*)\s*:")
# Generic scratch names seen in practice (`test`, `test1`/`test2`, `foo`, an
# unnamed `lemma "True" by simp`, ...) -- zero overlap with the 115 distinct
# names used across every genuinely verified final proof in this benchmark,
# so this has no observed false positives on real proofs.
_PROBE_NAMES = {
    "test",
    "test1",
    "test2",
    "test_ok",
    "ok_test",
    "foo",
    "bar",
    "p1",
    "sanity",
    "dummy",
    "scratch",
    "probe",
}


def looks_like_probe(thy_content: str) -> bool:
    """Whether a verified ``thy_content`` looks like an environment probe
    (a `find_theorems`/`thm` lookup, or a throwaway sanity-check lemma)
    rather than a real attempt at the exercise's actual theorem."""
    if "find_theorems" in thy_content:
        return True
    names = [n.lower() for n in _NAME_RE.findall(thy_content)]
    if not names:
        # No `lemma`/`theorem` statement at all (pure `thm` citations), or
        # an anonymous one (`lemma "True" by simp`) -- neither ever occurs
        # in a real submitted proof in this benchmark.
        return True
    return all(name in _PROBE_NAMES for name in names)


def lost_verifications(passes: pd.DataFrame) -> pd.DataFrame:
    """One row per run where some pass before the final one verified, but
    the final (highest-``pass_number``) pass did not."""
    records = []
    for run_id, group in passes.groupby("run_id"):
        g = group.sort_values("pass_number")
        final = g.iloc[-1]
        earlier = g.iloc[:-1]
        if not final["verified"] and earlier["verified"].any():
            last_verified = earlier.loc[earlier["verified"]].iloc[-1]
            records.append(
                {
                    "run_id": run_id,
                    "exercise_id": final["exercise_id"],
                    "model_name": final["model_name"],
                    "last_verified_pass": last_verified["pass_number"],
                    "last_verified_at": last_verified["created_at"],
                    "final_pass": final["pass_number"],
                    "final_at": final["created_at"],
                }
            )
    return pd.DataFrame(records)


def classify_by_content(repo: SupabaseRepository, lost: pd.DataFrame) -> pd.DataFrame:
    """Add ``same_content``, ``gamed``, and ``last_verified_is_probe`` columns.

    ``same_content``: did the last-verified pass and the final pass submit
    byte-for-byte the same ``thy_content``? On its own this is ambiguous
    between two very different situations, which is what ``gamed``
    disambiguates:

    - Genuine build flakiness: the exact same, legitimate theory verified
      once and then failed a fresh rebuild later -- a build-reliability
      problem (e.g. resource contention from concurrent runs), not anything
      the model did.
    - A deliberate retroactive correction: this project fixes a
      ``verified=True`` row it later determines was gamed (e.g. an
      ``axiomatization``-based or statement-free "proof" -- see
      ``query.isabelle._incomplete_commands``) the same way it fixes flaky
      builds -- by inserting a new final pass with the *same* ``thy_content``
      but ``verified=False`` and an error starting with
      ``query.isabelle.INCOMPLETE_PROOF_ERROR_PREFIX``. Checking the final
      pass's ``errors`` for that exact marker (rather than re-deriving
      "gamed" from the content itself) is what tells these apart: content-
      based detection would also catch unrelated, never-corrected rows that
      happen to share a reason (e.g. an old `check_in_isabelle`-probe with no
      statement of its own, never retroactively flagged).

    ``last_verified_is_probe`` (only meaningful when both ``same_content``
    and ``gamed`` are ``False``, since neither identical content nor a known
    gaming correction can also be a probe): was the last-verified pass
    actually a real attempt at the exercise, or a `check_in_isabelle` misused
    for exploration (see ``looks_like_probe``)? Only ``same_content=False,
    gamed=False, last_verified_is_probe=False`` runs are genuine cases of the
    model having a working proof and replacing it with something worse -- a
    real agent-behavior gap. A probe that happened to build clean was never
    a real answer, so its run isn't actually a lost verification at all,
    regardless of what the final pass did.

    Only pulls ``thy_content`` for the runs in ``lost`` -- a small, targeted
    query, never the whole ``benchmark`` table.
    """
    if lost.empty:
        return lost.assign(
            same_content=pd.Series(dtype=bool),
            gamed=pd.Series(dtype=bool),
            last_verified_is_probe=pd.Series(dtype=bool),
        )

    run_ids = [str(r) for r in lost["run_id"]]
    resp = (
        repo.client.table("benchmark")
        .select("run_id, pass_number, thy_content, errors")
        .in_("run_id", run_ids)
        .execute()
    )
    content_df = pd.DataFrame(resp.data)

    def _row_for(run_id: object, pass_number: object) -> pd.Series:
        contents = content_df.loc[content_df["run_id"] == str(run_id)]
        return contents.loc[contents["pass_number"] == pass_number].iloc[0]

    def _classify(row: pd.Series) -> pd.Series:
        last_verified_row = _row_for(row["run_id"], row["last_verified_pass"])
        final_row = _row_for(row["run_id"], row["final_pass"])
        last_verified_content = last_verified_row["thy_content"]
        same = last_verified_content.strip() == final_row["thy_content"].strip()
        gamed = any(
            e.startswith(INCOMPLETE_PROOF_ERROR_PREFIX) for e in final_row["errors"]
        )
        return pd.Series(
            {
                "same_content": same,
                "gamed": gamed,
                "last_verified_is_probe": (
                    False if same or gamed else looks_like_probe(last_verified_content)
                ),
            }
        )

    result = lost.copy()
    result[["same_content", "gamed", "last_verified_is_probe"]] = result.apply(
        _classify, axis=1
    )
    return result
