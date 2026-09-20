"""Per-topic performance: do models specialize -- i.e. is a model's accuracy
on a given topic meaningfully different from that same model's own overall
accuracy, rather than just topics being uniformly harder or easier for
everyone?
"""

from __future__ import annotations

import pandas as pd


def explode_topics(finals: pd.DataFrame, exercises: pd.DataFrame) -> pd.DataFrame:
    """One row per (run, topic): a run's outcome, tagged once per topic its
    exercise belongs to (an exercise can carry more than one topic)."""
    per_run = (
        finals.groupby(["exercise_id", "run_id"])
        .agg(verified=("verified", "max"), model_name=("model_name", "first"))
        .reset_index()
    )
    merged = per_run.merge(
        exercises[["exercise_id", "topics"]], on="exercise_id", how="left"
    )
    return (
        merged.explode("topics")
        .rename(columns={"topics": "topic"})
        .dropna(subset=["topic"])
    )


def topic_model_accuracy(exploded: pd.DataFrame, min_attempts: int = 1) -> pd.DataFrame:
    """(model, topic) accuracy, filtered to pairs seen at least
    `min_attempts` times -- below that, accuracy is mostly noise."""
    grouped = (
        exploded.groupby(["model_name", "topic"])
        .agg(attempts=("verified", "count"), verified=("verified", "sum"))
        .reset_index()
    )
    grouped = grouped[grouped["attempts"] >= min_attempts].copy()
    grouped["accuracy"] = grouped["verified"] / grouped["attempts"]
    return grouped


def specialization(topic_accuracy: pd.DataFrame) -> pd.DataFrame:
    """How far each (model, topic) accuracy sits from that model's own
    overall accuracy across every topic it has enough data for -- the signal
    for "unusually good/bad at this topic", as opposed to "generally strong".
    """
    per_model = topic_accuracy.groupby("model_name")[["verified", "attempts"]].sum()
    per_model["model_overall_accuracy"] = per_model["verified"] / per_model["attempts"]
    overall = per_model[["model_overall_accuracy"]].reset_index()

    merged = topic_accuracy.merge(overall, on="model_name")
    merged["delta_vs_own_average"] = (
        merged["accuracy"] - merged["model_overall_accuracy"]
    )
    return merged.sort_values("delta_vs_own_average", ascending=False)
