"""Judge whether verified proofs actually formalize their exercise's
intended theorem, not just something that happens to build clean.

Only touches `verified=True` final passes (~169 rows currently) -- an
unverified proof is already correctly scored as failed, nothing to judge.
Verdicts are cached locally under data/analysis/formalization_judge_cache.jsonl
(see analysis.formalization_judge's docstring for why this isn't written to
Supabase), and re-running only judges rows the cache doesn't already have,
so it's safe and cheap to re-invoke as new benchmark passes come in.
"""

import asyncio

import typer

from proyecto_isabelle.analysis.formalization_judge import (
    DEFAULT_JUDGE_MODEL,
    run_judge,
)

app = typer.Typer()


@app.command()
def main(
    judge_model: str = typer.Option(
        DEFAULT_JUDGE_MODEL,
        help="Model used as the judge, as '<provider>:<model>'. Should not be "
        "one of the benchmarked subjects, to avoid same-model bias.",
    ),
    limit: int | None = typer.Option(
        None, help="Judge at most N un-cached passes (for a cheap trial run)."
    ),
    concurrency: int = typer.Option(5, help="Max concurrent judge calls."),
) -> None:
    asyncio.run(
        run_judge(judge_model=judge_model, limit=limit, concurrency=concurrency)
    )


if __name__ == "__main__":
    app()
