"""LLM-as-judge check: does a verified proof's formal statement actually
capture the exercise's intended theorem, or did the model prove something
easier/different that still happens to build clean?

Isabelle's ``verified=True`` only means "this proof is logically valid for
whatever the theory states" -- it says nothing about whether the theory
states the right thing. A model can drop a hypothesis, narrow a general
claim to a specific case, or flip an inequality direction and still get a
green build. This module judges only ``verified=True`` final passes (an
unverified proof is already correctly scored as failed -- nothing to judge)
against the exercise's natural-language ``statement``, the only
human-authored, trustworthy reference available: ``proposed_thy_code``/
``corrected_thy_code`` are themselves unreviewed LLM output for 84 of 86
exercises (see ``analysis.data.load_exercises``), so they aren't a safe
formal ground truth to diff against.

Verdicts are cached locally (``data/analysis/formalization_judge_cache.jsonl``,
one JSON object per already-judged ``benchmark.id``), never written back to
Supabase: an LLM judge's verdict is probabilistic and the prompt will keep
changing, unlike the deterministic Isabelle re-verification in
``analysis.integrity``, so it shouldn't be mistaken for ground truth by other
tooling that reads ``benchmark`` directly.
"""

from __future__ import annotations

import asyncio
import json
from pathlib import Path
from typing import Literal

import pandas as pd
from jinja2 import Environment, FileSystemLoader, StrictUndefined
from pydantic import BaseModel, Field
from pydantic_ai import Agent

from proyecto_isabelle.query.llm.config import get_config
from proyecto_isabelle.query.proof_agent import _build_model
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.util import ANALYSIS_DIR

CACHE_PATH = ANALYSIS_DIR / "formalization_judge_cache.jsonl"
DEFAULT_JUDGE_MODEL = "anthropic:claude-opus-4-5-20251101"

_TEMPLATES_DIR = Path(__file__).parent.parent / "prompts" / "templates"


class FormalizationVerdict(BaseModel):
    """One judge's read of whether a verified proof's formal statement
    matches the exercise it was supposed to prove."""

    faithful: bool = Field(
        description="Overall: does the formal statement faithfully capture "
        "the natural-language statement?"
    )
    category: Literal[
        "exact_match",
        "equivalent_reformulation",
        "weaker_than_intended",
        "stronger_than_intended",
        "different_theorem",
        "cannot_determine",
    ]
    issues: list[str] = Field(
        default_factory=list,
        description="Specific discrepancies found; empty if faithful.",
    )
    reasoning: str = Field(description="One or two sentence justification.")


def _render_prompt(statement: str, source_title: str | None, thy_content: str) -> str:
    env = Environment(
        loader=FileSystemLoader(_TEMPLATES_DIR),
        trim_blocks=True,
        lstrip_blocks=True,
        undefined=StrictUndefined,
    )
    return env.get_template("formalization_judgment.md.jinja").render(
        statement=statement, source_title=source_title, thy_content=thy_content
    )


def _build_judge_agent(judge_model: str) -> Agent[None, FormalizationVerdict]:
    model = _build_model(judge_model, get_config())
    return Agent(model, output_type=FormalizationVerdict)


async def judge_one(
    agent: Agent[None, FormalizationVerdict],
    statement: str,
    source_title: str | None,
    thy_content: str,
) -> FormalizationVerdict:
    prompt = _render_prompt(statement, source_title, thy_content)
    result = await agent.run(prompt)
    return result.output


def load_cache() -> dict[int, dict]:
    """``{benchmark_id: cached judge record}`` for every row already judged."""
    if not CACHE_PATH.is_file():
        return {}
    records = {}
    for line in CACHE_PATH.read_text().splitlines():
        line = line.strip()
        if line:
            row = json.loads(line)
            records[row["benchmark_id"]] = row
    return records


def load_cache_df() -> pd.DataFrame:
    """Every cached judge record as a DataFrame, plus a ``self_judged``
    column: was the judge the same model as the one being judged?

    Verdicts where that's true (e.g. gpt-5.6-terra judging its own proofs,
    when judging is split across models to spread cost across API budgets)
    carry the usual self-preference-bias risk any LLM-as-judge setup has
    when the judge and the subject coincide, so callers should treat them
    with lower confidence rather than mixing them in unmarked.
    """
    cache = load_cache()
    if not cache:
        return pd.DataFrame()
    df = pd.DataFrame(cache.values())
    df["self_judged"] = df["judge_model"] == df["model_name"]
    return df


def faithful_rate_by_model(cache_df: pd.DataFrame) -> pd.DataFrame:
    """Per-model faithful rate among judged, verified passes, split by
    whether any of that model's judged rows were self-judged."""
    grouped = (
        cache_df.groupby("model_name")
        .agg(
            judged=("faithful", "count"),
            faithful=("faithful", "sum"),
            self_judged=("self_judged", "sum"),
        )
        .reset_index()
    )
    grouped["faithful_rate"] = grouped["faithful"] / grouped["judged"]
    return grouped.sort_values("faithful_rate")


def flagged_cases(cache_df: pd.DataFrame) -> pd.DataFrame:
    """Every judged pass the judge did *not* consider faithful, most
    recently judged first."""
    return cache_df.loc[~cache_df["faithful"]].sort_values(
        ["model_name", "exercise_name"]
    )


def _append_cache(record: dict) -> None:
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CACHE_PATH.open("a") as f:
        f.write(json.dumps(record) + "\n")
        f.flush()


def rows_to_judge(repo: SupabaseRepository) -> pd.DataFrame:
    """One row per run's true final pass, restricted to ``verified=True``:
    ``id, run_id, exercise_id, model_name, name, statement, source_title,
    thy_content``.

    Reuses ``analysis.data``'s final-pass selection (highest ``pass_number``
    per run across *every* pass, not just verified ones) rather than
    re-deriving it, so a run whose real final answer regressed to
    unverified — see ``analysis.integrity`` — is correctly excluded here
    too, instead of this module mistaking an earlier, superseded verified
    pass for the run's answer.
    """
    from proyecto_isabelle.analysis.data import (
        final_passes,
        load_benchmark_passes,
        load_exercises,
    )

    passes = load_benchmark_passes(repo)
    finals = final_passes(passes)
    verified_finals = finals.loc[finals["verified"]].copy()

    ids = [int(i) for i in verified_finals["id"]]
    resp = (
        repo.client.table("benchmark")
        .select("id, thy_content")
        .in_("id", ids)
        .execute()
    )
    content_by_id = {row["id"]: row["thy_content"] for row in resp.data}
    verified_finals["thy_content"] = verified_finals["id"].map(content_by_id)

    exercises = load_exercises(repo)
    return verified_finals.merge(
        exercises[["exercise_id", "name", "statement", "source_title"]],
        on="exercise_id",
        how="left",
    )


async def run_judge(
    judge_model: str = DEFAULT_JUDGE_MODEL,
    limit: int | None = None,
    concurrency: int = 5,
) -> None:
    """Judge every un-cached ``verified=True`` final pass, writing each
    verdict to the local cache as soon as it comes back (not batched at the
    end), so an interrupted run keeps whatever progress it made."""
    repo = SupabaseRepository()
    to_judge = rows_to_judge(repo)
    cached = load_cache()
    pending = to_judge.loc[~to_judge["id"].isin(cached.keys())]
    if limit is not None:
        pending = pending.head(limit)

    print(
        f"{len(to_judge)} verified final passes total, {len(cached)} already "
        f"cached, {len(pending)} to judge now with {judge_model}."
    )
    if pending.empty:
        return

    agent = _build_judge_agent(judge_model)
    lock = asyncio.Lock()
    semaphore = asyncio.Semaphore(concurrency)

    async def _judge_row(row: pd.Series) -> None:
        async with semaphore:
            verdict = await judge_one(
                agent, row.statement, row.source_title, row.thy_content
            )
        record = {
            "benchmark_id": int(row.id),
            "run_id": str(row.run_id),
            "exercise_id": int(row.exercise_id),
            "exercise_name": row["name"],
            "model_name": row.model_name,
            "judge_model": judge_model,
            **verdict.model_dump(),
        }
        async with lock:
            _append_cache(record)
        status = "OK" if verdict.faithful else "FLAGGED"
        print(f"  [{status}] {row['name']} / {row.model_name} ({verdict.category})")

    await asyncio.gather(*(_judge_row(row) for _, row in pending.iterrows()))
    print(f"Done. {len(pending)} newly judged, cache at {CACHE_PATH}")
