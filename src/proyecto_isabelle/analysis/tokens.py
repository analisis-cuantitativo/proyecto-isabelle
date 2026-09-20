"""Token-consumption metrics: per-model usage patterns, and whether token
spend correlates with exercise difficulty or with how many passes a run took.

`Benchmark.tokens_consumed` is cumulative input+output tokens through a given
pass (i.e. including every prior pass in the same run), so a run's *total*
spend is its final pass's value -- that's what every function here uses,
never a per-pass delta.
"""

from __future__ import annotations

import pandas as pd


def token_stats_by_model(finals: pd.DataFrame) -> pd.DataFrame:
    """Per (model, verified) group: count, mean/median/p90 total tokens."""
    grouped = finals.groupby(["model_name", "verified"])["tokens_consumed"].agg(
        count="count",
        mean_tokens="mean",
        median_tokens="median",
        p90_tokens=lambda s: s.quantile(0.9),
    )
    return grouped.reset_index()


def tokens_vs_difficulty(
    finals: pd.DataFrame, exercise_stats: pd.DataFrame
) -> pd.DataFrame:
    """Exercise-difficulty stats joined against that exercise's mean total
    tokens across every run -- the basis for the tokens/difficulty
    correlation."""
    per_exercise_tokens = (
        finals.groupby("exercise_id")["tokens_consumed"].mean().rename("mean_tokens")
    )
    return exercise_stats.merge(per_exercise_tokens, on="exercise_id")


def correlation_summary(tokens_vs_diff: pd.DataFrame) -> dict[str, float]:
    """Pearson/Spearman correlation between an exercise's mean token spend
    and how solvable it turned out to be (rate) or how many passes it took
    (count) -- the two natural "difficulty" readings against tokens."""
    return {
        "pearson_tokens_vs_solved_rate": tokens_vs_diff["mean_tokens"].corr(
            tokens_vs_diff["model_level_solved_rate"]
        ),
        "spearman_tokens_vs_solved_rate": tokens_vs_diff["mean_tokens"].corr(
            tokens_vs_diff["model_level_solved_rate"], method="spearman"
        ),
        "pearson_tokens_vs_avg_passes": tokens_vs_diff["mean_tokens"].corr(
            tokens_vs_diff["avg_passes_to_final"]
        ),
    }


def tokens_per_pass_curve(passes: pd.DataFrame) -> pd.DataFrame:
    """Median cumulative tokens by (model, pass_number) -- how fast each
    model burns through its token budget across successive Isabelle checks
    within a run."""
    return (
        passes.groupby(["model_name", "pass_number"])["tokens_consumed"]
        .median()
        .reset_index()
    )
