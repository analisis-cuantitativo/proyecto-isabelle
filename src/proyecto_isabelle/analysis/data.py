"""Data loading for the offline benchmark analysis.

Pulls per-pass rows from the Supabase `benchmark` table (via
`SupabaseRepository.list_full_benchmark_rows`) and exercise metadata from
`exercise_full` (via `list_all_exercises`), and reads local
`data/run_logs/<run_id>.jsonl` files for the qualitative detail (thinking,
output-validator retries) that never makes it into `benchmark` at all.

Model names get canonicalized on load: a handful of historical rows were
written as ``"anthropic/claude-..."`` instead of the pydantic_ai
``"anthropic:claude-..."`` convention every other row (and the rest of this
codebase) uses. Left alone, every metric below would silently treat that as
a second, much-smaller "model" instead of folding it into Sonnet's numbers.
"""

from __future__ import annotations

import json
import re
from typing import Any

import pandas as pd

from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.util import RUN_LOGS_DIR

_SLASH_SEPARATED_PROVIDERS = (
    "anthropic",
    "openai-responses",
    "openai",
    "google-gla",
    "deepseek",
    "moonshotai",
)


def canonicalize_model_name(model_name: str) -> str:
    """Rewrite a ``"<provider>/<model>"`` name to ``"<provider>:<model>"``.

    Leaves already-canonical (``:``-separated) names untouched.
    """
    for provider in _SLASH_SEPARATED_PROVIDERS:
        prefix = f"{provider}/"
        if model_name.startswith(prefix):
            return f"{provider}:{model_name[len(prefix) :]}"
    return model_name


def display_model_name(model_name: str) -> str:
    """Short label for figures/tables: drops the provider and a trailing
    ``YYYYMMDD`` snapshot date, and writes dashed versions with a dot
    (``"anthropic:claude-sonnet-4-5-20250929"`` -> ``"claude-sonnet-4.5"``).
    """
    name = re.sub(r"-\d{8}$", "", canonicalize_model_name(model_name).split(":", 1)[-1])
    return re.sub(r"(?<=\d)-(?=\d)", ".", name)


def load_benchmark_passes(
    repo: SupabaseRepository, version: int | None = None
) -> pd.DataFrame:
    """One row per real ``check_in_isabelle`` pass, across every run/model.

    Columns: ``run_id, pass_number, exercise_id, model_name,
    was_given_the_correct_thy_statement, verified, errors, num_errors,
    max_num_of_passes, hit_retry_budget, tokens_consumed, created_at,
    version, agent_revision``.

    ``version`` restricts the load to one benchmark campaign. ``None`` loads
    every campaign, which is fine for a cross-campaign comparison but wrong
    for a headline rate: campaigns ran against different agent revisions, so
    a pooled rate is an average over incomparable conditions. Callers that
    report one number should pass a version — ``build_report`` does.
    """
    rows = repo.list_full_benchmark_rows(version=version)
    df = pd.DataFrame(rows)
    df["model_name_raw"] = df["model_name"]
    df["model_name"] = df["model_name"].map(canonicalize_model_name)
    df["created_at"] = pd.to_datetime(df["created_at"])
    df["num_errors"] = df["errors"].map(len)
    return df


def final_passes(passes: pd.DataFrame) -> pd.DataFrame:
    """One row per ``run_id``: its highest-``pass_number`` row.

    That's the run's final, independently-reverified answer (see
    ``sync.models.Benchmark``'s docstring) -- earlier passes are just the
    agent's intermediate attempts and shouldn't count toward whether the run
    "solved" the exercise.
    """
    idx = passes.groupby("run_id")["pass_number"].idxmax()
    return passes.loc[idx].reset_index(drop=True)


def load_exercises(repo: SupabaseRepository) -> pd.DataFrame:
    """One row per benchmarkable exercise: ``exercise_id, name, topics``
    (a ``list[str]``, possibly empty), ``msc_code, source_title, statement``.
    """
    exercises = repo.list_all_exercises()
    return pd.DataFrame(
        {
            "exercise_id": ex.id,
            "name": ex.name,
            "topics": ex.topics or [],
            "msc_code": ex.msc_code,
            "source_title": ex.source.title,
            "statement": ex.statement,
        }
        for ex in exercises
    )


def load_run_log(run_id: str) -> list[dict[str, Any]] | None:
    """Events for one run's local JSONL log, or ``None`` if it isn't local
    (e.g. it ran on a different machine)."""
    path = RUN_LOGS_DIR / f"{run_id}.jsonl"
    if not path.is_file():
        return None
    events = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            events.append(json.loads(line))
    return events


def available_run_log_ids() -> set[str]:
    if not RUN_LOGS_DIR.is_dir():
        return set()
    return {p.stem for p in RUN_LOGS_DIR.glob("*.jsonl")}
