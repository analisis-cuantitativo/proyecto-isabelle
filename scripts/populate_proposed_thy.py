import typer
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax

from proyecto_isabelle.prompts import (
    PROMPT_FOR_THY_CONTENT_PROPOSAL,
    extract_thy_content,
)
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.query.llm import batch as llm_batch
from proyecto_isabelle.query.llm.models import LLMResponse
from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.sync.repository import SupabaseRepository

app = typer.Typer()
console = Console()

MODEL = "anthropic/claude-opus-4-6"
MAX_TOKENS = 4096 * 6
MAX_RETRIES = 3
DEFAULT_BATCH_SIZE = 50
DEFAULT_POLL_INTERVAL_SECONDS = 30.0


def _process_llm_response(exercise: Exercise, response: LLMResponse) -> Exercise | None:
    """Extract + verify a single LLM response for an exercise.

    Returns the exercise updated with verified `proposed_thy_code`, or None
    if this response should be treated as a failed attempt (and retried).
    """
    if not response.success:
        console.print(
            Panel(
                f"[red]LLM request failed[/red]\n{response.error or 'Unknown error'}",
                title=f"{exercise.name}: Error",
                border_style="red",
            )
        )
        return None

    if response.thinking:
        console.print(
            Panel(
                response.thinking,
                title=f"{exercise.name}: Thinking",
                border_style="dim",
            )
        )

    thy_content = extract_thy_content(response.content or "")
    if thy_content is None:
        console.print(
            Panel(
                "[red]Failed to extract thy content from response[/red]",
                title=f"{exercise.name}: Extraction Error",
                border_style="red",
            )
        )
        return None

    console.print(
        Panel(
            Syntax(thy_content, "isabelle", theme="monokai"),
            title=f"{exercise.name}: Extracted Thy Content",
            border_style="green",
        )
    )

    # A statement skeleton is expected to keep `sorry` as its proof
    # placeholder, so `allow_incomplete=True` accepts it as long as it
    # parses and type-checks (against the Benchmark heap, imports honoured).
    isabelle_result = query_content(thy_content, allow_incomplete=True)

    if not isabelle_result.verified:
        console.print(
            Panel(
                f"[red]Isabelle verification failed[/red]\n{isabelle_result.errors or 'Unknown error'}",
                title=f"{exercise.name}: Verification Error",
                border_style="red",
            )
        )
        return None

    console.print(f"[green]Verification successful for {exercise.name}![/green]")
    return exercise.model_copy(update={"proposed_thy_code": thy_content})


def populate_proposed_thy_for_exercise(exercise: Exercise) -> Exercise:
    console.print(
        Panel(
            f"[bold]{exercise.name}[/bold]",
            title="Processing Exercise",
            border_style="blue",
        )
    )

    for attempt in range(1, MAX_RETRIES + 1):
        if attempt > 1:
            console.print(f"[yellow]Retry attempt {attempt}/{MAX_RETRIES}[/yellow]")

        prompt = PROMPT_FOR_THY_CONTENT_PROPOSAL.format(exercise=exercise.statement)
        console.print(
            f"[blue]Querying {MODEL} for a formalization of {exercise.statement}[/blue]"
        )
        response = ask(
            prompt=prompt,
            model=MODEL,
            temperature=1.0,
            max_tokens=MAX_TOKENS,
            thinking_budget=MAX_TOKENS // 3,
        )

        updated = _process_llm_response(exercise, response)
        if updated is not None:
            return updated

    console.print(
        Panel(
            f"[red]Failed to generate valid thy content after {MAX_RETRIES} attempts[/red]",
            title="Max Retries Exceeded",
            border_style="red",
        )
    )
    raise typer.Exit(code=1)


def _chunked(items: list[Exercise], size: int) -> list[list[Exercise]]:
    return [items[i : i + size] for i in range(0, len(items), size)]


def _run_batch_round(
    exercises: list[Exercise], attempt: int, poll_interval: float
) -> dict[str, LLMResponse]:
    """Submit one Message Batch (one request per exercise) and block until
    results are in. custom_ids are just positional indices into `exercises`,
    which sidesteps any character restrictions or name collisions."""
    prompts = {
        str(i): PROMPT_FOR_THY_CONTENT_PROPOSAL.format(exercise=ex.statement)
        for i, ex in enumerate(exercises)
    }

    console.print(
        f"[blue]Submitting batch round {attempt}/{MAX_RETRIES} "
        f"({len(prompts)} exercise(s)) to {MODEL}[/blue]"
    )

    def _on_poll(current_batch) -> None:
        counts = current_batch.request_counts
        console.print(
            f"[dim]batch {current_batch.id}: {current_batch.processing_status} "
            f"(succeeded={counts.succeeded} errored={counts.errored} "
            f"processing={counts.processing})[/dim]"
        )

    return llm_batch.run_batch(
        prompts,
        model=MODEL.removeprefix("anthropic/"),
        temperature=1.0,
        max_tokens=MAX_TOKENS,
        thinking_budget=MAX_TOKENS // 3,
        poll_interval=poll_interval,
        on_poll=_on_poll,
    )


def _run_batch_chunk(
    repo: SupabaseRepository, chunk: list[Exercise], poll_interval: float
) -> tuple[int, list[Exercise]]:
    """Run the retry rounds for one chunk of exercises. Returns
    (successful_count, exercises_still_failing_after_max_retries)."""
    pending = chunk
    successful = 0

    for attempt in range(1, MAX_RETRIES + 1):
        if not pending:
            break

        results = _run_batch_round(pending, attempt, poll_interval)

        still_pending: list[Exercise] = []
        for i, exercise in enumerate(pending):
            response = results.get(str(i))
            if response is None:
                console.print(f"[red]No result returned for {exercise.name}[/red]")
                still_pending.append(exercise)
                continue

            updated = _process_llm_response(exercise, response)
            if updated is None:
                still_pending.append(exercise)
                continue

            repo.write(updated)
            successful += 1

        pending = still_pending

    return successful, pending


@app.command()
def run(exercise_name: str) -> None:
    repo = SupabaseRepository()
    exercise = repo.read_as_exercise(exercise_name)
    new_exercise = populate_proposed_thy_for_exercise(exercise)
    repo.write(new_exercise)
    console.print(f"[green]Successfully updated exercise: {exercise_name}[/green]")


@app.command()
def run_all(
    batch_size: int = typer.Option(
        DEFAULT_BATCH_SIZE,
        help="Max exercises per Message Batch submission.",
    ),
    poll_interval: float = typer.Option(
        DEFAULT_POLL_INTERVAL_SECONDS,
        help="Seconds between batch status checks.",
    ),
) -> None:
    """Populate proposed_thy_code for every exercise missing it, using
    Anthropic's Message Batches API instead of one synchronous request per
    exercise. This avoids holding a long-lived HTTP connection open per
    exercise, which is what was timing out."""
    repo = SupabaseRepository()
    all_exercises = repo.read_with_empty_proposed_thy()

    if not all_exercises:
        console.print("[yellow]No exercises with empty proposed thy found[/yellow]")
        return

    console.print(f"[blue]Found {len(all_exercises)} exercises to process[/blue]")

    successful = 0
    failed_exercises: list[Exercise] = []

    chunks = _chunked(all_exercises, batch_size)
    for chunk_num, chunk in enumerate(chunks, 1):
        console.print(
            Panel(
                f"Chunk {chunk_num}/{len(chunks)} — {len(chunk)} exercise(s)",
                border_style="blue",
            )
        )
        chunk_successful, chunk_failed = _run_batch_chunk(repo, chunk, poll_interval)
        successful += chunk_successful
        failed_exercises.extend(chunk_failed)

    for exercise in failed_exercises:
        console.print(
            f"[red]Failed to generate valid thy content after {MAX_RETRIES} "
            f"attempts: {exercise.name}[/red]"
        )

    console.print(
        Panel(
            f"[green]Successful: {successful}[/green]\n"
            f"[red]Failed: {len(failed_exercises)}[/red]",
            title="Summary",
            border_style="blue",
        )
    )


if __name__ == "__main__":
    app()
