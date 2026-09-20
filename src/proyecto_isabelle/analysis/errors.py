"""Heuristic categorization of Isabelle failure messages, for the "lessons
learned" section: which failure modes are most common overall, which ones a
given model gets stuck on (survive to the run's final, unfixed pass), and how
often the model never even reaches Isabelle (bounced by the output validator
for still containing `sorry`/`oops`, or for not having called
`check_in_isabelle` at all -- see `query.proof_agent.build_proof_agent`).

Categories are ordered most-specific-first and matched by regex against each
individual error string in `benchmark.errors`; a message can only land in one
category (the first pattern that matches), with an `"other"` catch-all.
"""

from __future__ import annotations

import re

import pandas as pd

from proyecto_isabelle.analysis.data import load_run_log

_CATEGORY_PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("sorry_or_oops", re.compile(r"\bsorry\b|\boops\b", re.IGNORECASE)),
    ("timeout", re.compile(r"\btimed out\b|\btimeout\b", re.IGNORECASE)),
    (
        "malformed_or_syntax",
        re.compile(r"malformed|inner syntax error|outer syntax error", re.IGNORECASE),
    ),
    (
        "undefined_name",
        re.compile(
            r"\bundefined\b|unknown fact|unknown constant|no such (constant|fact)"
            r"|not a constant|inconsistent sort constraints",
            re.IGNORECASE,
        ),
    ),
    (
        "type_error",
        re.compile(
            r"type unification failed|type mismatch|incompatible type"
            r"|clash of types",
            re.IGNORECASE,
        ),
    ),
    (
        "import_error",
        re.compile(
            r"bad theory import|unknown theory|cannot find theory", re.IGNORECASE
        ),
    ),
    (
        "unfinished_proof",
        re.compile(
            r"failed to finish proof|failed to apply (initial )?proof method"
            r"|unfinished subgoals?",
            re.IGNORECASE,
        ),
    ),
    (
        "build_crash",
        re.compile(r"exception|internal error|out of memory", re.IGNORECASE),
    ),
]


def categorize(message: str) -> str:
    for category, pattern in _CATEGORY_PATTERNS:
        if pattern.search(message):
            return category
    return "other"


def categorize_passes(passes: pd.DataFrame) -> pd.DataFrame:
    """One row per pass that recorded at least one Isabelle error, tagged
    with a single category.

    A logical Isabelle error is reported as *several* entries in
    ``benchmark.errors`` (the failing command's message, its goal state, its
    source location), so categorizing line-by-line mostly matches goal-state
    text against nothing and dumps it in ``"other"``. Instead, every error
    line for a pass is joined into one blob and categorized as a whole,
    picking the first (most specific) pattern that matches anywhere in it.
    """
    with_errors = passes.loc[passes["errors"].map(len) > 0].copy()
    with_errors["category"] = with_errors["errors"].map(
        lambda lines: categorize("\n".join(lines))
    )
    return with_errors[
        ["run_id", "exercise_id", "model_name", "pass_number", "verified", "category"]
    ]


def category_frequency(categorized_passes: pd.DataFrame) -> pd.DataFrame:
    """How often each error category shows up per model, across every pass
    (not just final ones) -- the raw frequency a model runs into each
    failure mode at all, whether or not it later recovers from it."""
    return (
        categorized_passes.groupby(["model_name", "category"])
        .size()
        .rename("count")
        .reset_index()
        .sort_values("count", ascending=False)
    )


def unresolved_categories(
    passes: pd.DataFrame, categorized_passes: pd.DataFrame
) -> pd.DataFrame:
    """Error categories present on a run's *final* pass, restricted to runs
    that ended unverified -- i.e. the failure mode the model never got past,
    as opposed to an error it hit and then fixed on a later pass."""
    finals = passes.loc[passes.groupby("run_id")["pass_number"].idxmax()]
    failed_finals = finals.loc[~finals["verified"], ["run_id", "pass_number"]]
    on_final_failure = categorized_passes.merge(
        failed_finals, on=["run_id", "pass_number"]
    )
    return (
        on_final_failure.groupby(["model_name", "category"])
        .size()
        .rename("count")
        .reset_index()
        .sort_values("count", ascending=False)
    )


def retry_event_counts(run_ids: list[str]) -> pd.DataFrame:
    """Per-run count of output-validator retries recorded in the local
    JSONL log (the model submitting `sorry`/`oops`, or a final answer it
    never ran through `check_in_isabelle`) -- these never reach Isabelle, so
    `benchmark.errors` has no record of them at all. Runs with no local log
    file (e.g. executed on a different machine) are simply skipped, so the
    result only covers whatever fraction of runs happened locally.
    """
    records = []
    for run_id in run_ids:
        events = load_run_log(run_id)
        if events is None:
            continue
        records.append(
            {
                "run_id": run_id,
                "num_retries": sum(1 for e in events if e["type"] == "retry"),
            }
        )
    return pd.DataFrame(records)
