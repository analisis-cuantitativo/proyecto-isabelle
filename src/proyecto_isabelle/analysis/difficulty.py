"""Per-exercise difficulty: which exercises are hardest/most trivial across
models, based on `benchmark`'s final (independently-reverified) pass per run.
"""

from __future__ import annotations

import pandas as pd


def exercise_difficulty(finals: pd.DataFrame, exercises: pd.DataFrame) -> pd.DataFrame:
    """One row per exercise, with two difficulty proxies:

    - ``run_level_verified_rate``: of every run (any model, any number of
      retries) ever attempted against this exercise, the fraction whose
      final pass verified. Sensitive to how many times a model was re-run.
    - ``model_level_solved_rate``: of every model that ever attempted this
      exercise, the fraction that solved it on *some* run (matches the
      dashboard's "verified if any run verified" convention). The more
      honest per-model difficulty signal, since it doesn't let one model's
      repeated retries dominate the count.
    """
    per_run = (
        finals.groupby(["exercise_id", "run_id"])
        .agg(
            verified=("verified", "max"),
            pass_number=("pass_number", "max"),
            hit_retry_budget=("hit_retry_budget", "max"),
            model_name=("model_name", "first"),
        )
        .reset_index()
    )

    stats = (
        per_run.groupby("exercise_id")
        .agg(
            num_runs=("run_id", "count"),
            num_verified_runs=("verified", "sum"),
            avg_passes_to_final=("pass_number", "mean"),
            retry_budget_hit_rate=("hit_retry_budget", "mean"),
        )
        .reset_index()
    )

    per_model_solved = (
        per_run.groupby(["exercise_id", "model_name"])["verified"].max().reset_index()
    )
    by_exercise = per_model_solved.groupby("exercise_id")
    coverage = pd.DataFrame(
        {
            "num_models_attempted": by_exercise["model_name"].nunique(),
            "num_models_that_solved_it": by_exercise["verified"].sum(),
        }
    ).reset_index()

    stats = stats.merge(coverage, on="exercise_id")
    stats["run_level_verified_rate"] = stats["num_verified_runs"] / stats["num_runs"]
    stats["model_level_solved_rate"] = (
        stats["num_models_that_solved_it"] / stats["num_models_attempted"]
    )

    return stats.merge(exercises, on="exercise_id", how="left").sort_values(
        "model_level_solved_rate"
    )


def hardest(stats: pd.DataFrame, n: int = 15) -> pd.DataFrame:
    """The `n` exercises no model (or the fewest models) ever solved,
    unsolved-by-everyone first, tie-broken by how many models tried."""
    return stats.sort_values(
        ["model_level_solved_rate", "num_models_attempted"], ascending=[True, False]
    ).head(n)


def easiest(stats: pd.DataFrame, n: int = 15) -> pd.DataFrame:
    """The `n` exercises solved by every model that attempted them, ranked
    by how few passes that took on average -- the "trivial" end."""
    solved_by_all = stats[
        (stats["model_level_solved_rate"] == 1.0) & (stats["num_models_attempted"] > 1)
    ]
    return solved_by_all.sort_values(
        ["avg_passes_to_final", "retry_budget_hit_rate"]
    ).head(n)
