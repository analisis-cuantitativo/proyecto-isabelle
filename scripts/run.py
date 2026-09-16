"""Prove a single exercise using the pydantic_ai-based proof agent.

Demonstrates the scaffolding in `query/proof_agent.py` + `prompts/render.py`:
the agent verifies its own attempts against Isabelle mid-run (via the
`check_in_isabelle` tool) before returning, and we still re-verify the final
answer here independently, since the agent's self-report isn't authoritative.
"""

import asyncio
import itertools
import json
from pathlib import Path
from uuid import uuid4

import typer
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax

from proyecto_isabelle.parse import thy
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.proof_agent import (
    DEFAULT_MODEL,
    IsabelleCheck,
    ProofAttempt,
    ProofBudgetExceeded,
    ProofResult,
    prove_exercise,
)
from proyecto_isabelle.query.run_log import RunLogWriter
from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.util import PROOFS_DIR, ROOT_DIR, sanitize_model_name

app = typer.Typer()
console = Console()

# Dev-only cache so re-runs (e.g. while debugging save_benchmark/Supabase
# issues) don't re-query the LLM for an exercise+model already tried.
CACHE_DIR = ROOT_DIR / "data" / "cache" / "proof_agent"


def _cache_path(exercise_name: str, model_name: str) -> Path:
    return CACHE_DIR / f"{exercise_name}__{sanitize_model_name(model_name)}.json"


def _load_cached_result(cache_path: Path) -> ProofResult | None:
    if not cache_path.is_file():
        return None
    data = json.loads(cache_path.read_text())
    return ProofResult(
        attempt=ProofAttempt.model_validate(data["attempt"]),
        checks=[IsabelleCheck.model_validate(c) for c in data["checks"]],
        request_count=data["request_count"],
        total_tokens=data["total_tokens"],
        max_isabelle_checks=data["max_isabelle_checks"],
    )


def _save_cached_result(cache_path: Path, result: ProofResult) -> None:
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    cache_path.write_text(
        json.dumps(
            {
                "attempt": result.attempt.model_dump(mode="json"),
                "checks": [c.model_dump(mode="json") for c in result.checks],
                "request_count": result.request_count,
                "total_tokens": result.total_tokens,
                "max_isabelle_checks": result.max_isabelle_checks,
            },
            indent=2,
        )
    )


def _prove_and_save_one(
    repo: SupabaseRepository,
    exercise: Exercise,
    model_name: str,
    with_proof: bool,
    with_proposed_skeleton: bool,
    max_isabelle_checks: int,
    use_cache: bool,
    build_timeout_seconds: int,
    max_empty_response_retries: int = 2,
) -> bool:
    """Prove one exercise, persist a `benchmark` row per pass, and — if it
    verifies — save the .thy file to disk. Returns whether it verified.

    Every pass (each real `check_in_isabelle` call, plus the final
    independent re-verification below) is persisted to Supabase as soon as
    it happens, via `on_check`/`save_benchmark_pass` — not batched into one
    insert at the end — so a run's progress survives a crash partway through
    it, including one raised by an exception type nothing here anticipated.

    ``max_empty_response_retries`` retries the whole exercise with a *fresh*
    run (empty message history) when a run aborts having made zero Isabelle
    checks — the signature of some providers (deepseek-reasoner in
    particular) occasionally returning a completely empty first response.
    pydantic_ai's own recovery for that resubmits the conversation with the
    empty response already baked into history, which some providers'
    servers then reject outright as an invalid message — so retrying within
    the same run can't help; only starting over with clean history can. A
    budget-exceeded run that made at least one real check isn't retried:
    that's genuine exhaustion after real progress, not a fluke.

    Never raises for expected failure modes (budget exhausted, verification
    failed): those are reported to the console and folded into the return
    value, so a caller looping over many exercises (`run_all`) can continue
    past one bad exercise instead of aborting the whole batch.
    """
    exercise_name = exercise.name
    assert exercise.statement is not None

    cache_path = _cache_path(exercise_name, model_name)
    proof_result = _load_cached_result(cache_path) if use_cache else None

    # A cache hit replays a previous run's result with no fresh LLM/Isabelle
    # interactions to observe, so there's nothing for a local run log to
    # record — `run_id` still gets a fresh benchmark row, just no log file.
    run_id = uuid4()
    writer = None

    pass_numbers = itertools.count(1)

    def on_check(check: IsabelleCheck) -> None:
        repo.save_benchmark_pass(
            exercise=exercise,
            check=check,
            model_name=model_name,
            max_num_of_passes=max_isabelle_checks,
            run_id=run_id,
            pass_number=next(pass_numbers),
        )

    if proof_result is not None:
        console.print(f"[dim]{exercise_name}: using cached agent result[/dim]")
        # A cache hit never went through `on_check` live, so replay it here
        # to end up with the same rows a fresh run would have produced.
        for check in proof_result.checks:
            on_check(check)
    else:
        for attempt_num in range(1, max_empty_response_retries + 2):
            writer = RunLogWriter(run_id)
            writer.log_started(
                exercise_name,
                model_name,
                max_isabelle_checks,
                exercise_statement=exercise.statement,
                proof=exercise.proof if with_proof else None,
            )
            try:
                proof_result = asyncio.run(
                    prove_exercise(
                        exercise=exercise.statement,
                        proof=exercise.proof if with_proof else None,
                        proposed_thy_code=(
                            exercise.proposed_thy_code
                            if with_proposed_skeleton
                            else None
                        ),
                        model_name=model_name,
                        max_isabelle_checks=max_isabelle_checks,
                        run_logger=writer,
                        build_timeout_seconds=build_timeout_seconds,
                        on_check=on_check,
                    )
                )
                break
            except ProofBudgetExceeded as e:
                console.print(
                    Panel(
                        f"[red]{e}[/red]",
                        title=f"{exercise_name}: budget exhausted",
                        border_style="red",
                    )
                )
                writer.log_finished(verified=False, hit_retry_budget=True)
                if not e.checks:
                    # The model never called check_in_isabelle even once —
                    # nothing was persisted, so a fresh run (new run_id,
                    # empty history) is safe to try again.
                    if attempt_num <= max_empty_response_retries:
                        console.print(
                            f"[yellow]{exercise_name}: empty response from "
                            f"the model, retrying with a fresh run "
                            f"({attempt_num}/{max_empty_response_retries})"
                            "[/yellow]"
                        )
                        run_id = uuid4()
                        continue
                    console.print(
                        f"[yellow]{exercise_name}: no Isabelle checks were "
                        "made after retrying, nothing to save[/yellow]"
                    )
                    return False
                # Every check in e.checks was already saved live via
                # on_check — just flag the run now that we know it hit the
                # retry budget.
                repo.mark_run_hit_retry_budget(run_id)
                return False

        assert proof_result is not None  # loop above only exits via break/return
        _save_cached_result(cache_path, proof_result)

    console.print(
        f"[dim]{exercise_name}: {len(proof_result.checks)} Isabelle check(s), "
        f"{proof_result.request_count} model request(s)[/dim]"
    )
    attempt = proof_result.attempt

    console.print(
        Panel(
            Syntax(attempt.thy_content, "isabelle", theme="monokai"),
            title=f"{exercise_name}: {attempt.theory_name}",
            border_style="green",
        )
    )

    # Independent re-verification: the agent's self-reported `verified` is
    # not authoritative, and this also becomes the run's final pass row.
    result = query_content(
        attempt.thy_content, mode="build", timeout_seconds=build_timeout_seconds
    )
    if writer:
        writer.log_event(
            {
                "type": "final_reverification",
                "verified": result.verified,
                "errors": result.errors,
            }
        )
        writer.log_finished(
            verified=result.verified,
            request_count=proof_result.request_count,
            total_tokens=proof_result.total_tokens,
        )
    on_check(
        IsabelleCheck(
            thy_content=attempt.thy_content,
            verified=result.verified,
            errors=result.errors,
            tokens_consumed=proof_result.total_tokens,
        )
    )

    if not result.verified:
        console.print(
            Panel(
                f"[red]{result.message}[/red]\n" + "\n".join(result.errors),
                title=f"{exercise_name}: verification failed",
                border_style="red",
            )
        )
        return False

    proof_dir = (
        PROOFS_DIR
        / f"exercise={exercise_name}"
        / f"model={sanitize_model_name(model_name)}"
    )
    proof_dir.mkdir(parents=True, exist_ok=True)
    thy_path = proof_dir / f"{attempt.theory_name}.thy"
    thy.save_text(attempt.thy_content, thy_path)

    console.print(f"[green]{exercise_name}: verified and saved to {thy_path}[/green]")
    return True


@app.command()
def run(
    exercise_name: str,
    model_name: str = typer.Option(
        DEFAULT_MODEL,
        help="Model, as '<provider>:<model>' (see util.constants.Models).",
    ),
    with_proof: bool = typer.Option(
        True, help="Include the exercise's natural-language proof in the prompt."
    ),
    with_proposed_skeleton: bool = typer.Option(
        True,
        help="Include the exercise's already-generated proposed_thy_code skeleton.",
    ),
    max_isabelle_checks: int = typer.Option(
        5, help="Max check_in_isabelle calls the agent may make before it must submit."
    ),
    use_cache: bool = typer.Option(
        True,
        help=(
            "Reuse a cached agent result for this exercise+model instead of "
            "re-querying the LLM. Dev convenience, e.g. while iterating on "
            "save_benchmark_pass — pass --no-use-cache to force a fresh query."
        ),
    ),
    build_timeout_seconds: int = typer.Option(
        (60 * 20),
        help=(
            "Timeout in seconds the DeepIsaHOL server gets for each isabelle "
            "build (per check_in_isabelle call and the final re-verification). "
            "Raise this if you see 'Build timed out' failures."
        ),
    ),
    max_empty_response_retries: int = typer.Option(
        2,
        help=(
            "Retries with a fresh run (empty history) when a provider "
            "returns a completely empty first response (some providers, "
            "e.g. deepseek-reasoner, occasionally do this, and the poisoned "
            "history can't recover within the same run)."
        ),
    ),
) -> None:
    repo = SupabaseRepository()
    exercise = repo.read_as_exercise(exercise_name)
    if exercise.statement is None:
        console.print(f"[red]Exercise {exercise_name} has no statement.[/red]")
        raise typer.Exit(code=1)

    console.print(
        Panel(f"[bold]{exercise_name}[/bold]", title="Proving", border_style="blue")
    )

    verified = _prove_and_save_one(
        repo,
        exercise,
        model_name,
        with_proof,
        with_proposed_skeleton,
        max_isabelle_checks,
        use_cache,
        build_timeout_seconds,
        max_empty_response_retries,
    )
    if not verified:
        raise typer.Exit(code=1)


@app.command()
def run_all(
    model_name: str = typer.Option(
        DEFAULT_MODEL,
        help="Model, as '<provider>:<model>' (see util.constants.Models).",
    ),
    with_proof: bool = typer.Option(
        True, help="Include each exercise's natural-language proof in the prompt."
    ),
    with_proposed_skeleton: bool = typer.Option(
        True,
        help="Include each exercise's already-generated proposed_thy_code skeleton.",
    ),
    max_isabelle_checks: int = typer.Option(
        5, help="Max check_in_isabelle calls the agent may make before it must submit."
    ),
    use_cache: bool = typer.Option(
        True, help="Reuse a cached agent result per exercise+model when available."
    ),
    limit: int = typer.Option(
        0,
        help="Only process the first N exercises (0 = no limit). Useful for a dry run.",
    ),
    build_timeout_seconds: int = typer.Option(
        (60 * 20),
        help=(
            "Timeout in seconds the DeepIsaHOL server gets for each isabelle "
            "build (per check_in_isabelle call and the final re-verification). "
            "Raise this if you see 'Build timed out' failures."
        ),
    ),
    max_empty_response_retries: int = typer.Option(
        2,
        help=(
            "Retries with a fresh run (empty history) when a provider "
            "returns a completely empty first response (some providers, "
            "e.g. deepseek-reasoner, occasionally do this, and the poisoned "
            "history can't recover within the same run)."
        ),
    ),
) -> None:
    """Prove every exercise not yet benchmarked with `model_name`.

    Resumable: exercises that already have a `benchmark` row for this model
    are skipped (via `get_missing_exercises_by_model`), so re-running after
    an interruption or a handful of failures only retries what's left.

    That same call orders exercises no model has ever attempted before ones
    other models have already covered, so `--limit` (or an interrupted run)
    grows the benchmark's overall exercise coverage first rather than piling
    up repeat attempts on already-covered exercises.
    """
    repo = SupabaseRepository()
    exercises = repo.get_missing_exercises_by_model(model_name)
    if limit:
        exercises = exercises[:limit]

    console.print(
        f"[blue]{len(exercises)} exercise(s) to prove with {model_name}[/blue]"
    )

    verified_count = 0
    failed: list[str] = []

    for i, exercise in enumerate(exercises, 1):
        console.print(
            Panel(
                f"[bold]{exercise.name}[/bold] ({i}/{len(exercises)})",
                border_style="blue",
            )
        )
        if exercise.statement is None:
            console.print(f"[yellow]{exercise.name}: no statement, skipping[/yellow]")
            failed.append(exercise.name)
            continue

        try:
            verified = _prove_and_save_one(
                repo,
                exercise,
                model_name,
                with_proof,
                with_proposed_skeleton,
                max_isabelle_checks,
                use_cache,
                build_timeout_seconds,
                max_empty_response_retries,
            )
        except Exception as e:
            console.print(
                f"[red]{exercise.name}: unexpected error "
                f"({type(e).__name__}): {e}[/red]"
            )
            verified = False

        if verified:
            verified_count += 1
        else:
            failed.append(exercise.name)

    summary = f"[green]Verified: {verified_count}/{len(exercises)}[/green]"
    if failed:
        summary += "\n[red]Failed:[/red] " + ", ".join(failed)
    console.print(Panel(summary, title="Summary", border_style="blue"))


if __name__ == "__main__":
    app()
