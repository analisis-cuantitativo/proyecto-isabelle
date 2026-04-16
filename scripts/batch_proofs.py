"""
En este script, iteramos sobre los ejercicios en `data/exercises`
(o `data/exercises_with_proof`), revisando si un modelo específico
es capaz de resolverlos.
"""

import random
from pathlib import Path
from typing import Annotated, Any

import typer
from rich.console import Console
from rich.progress import Progress, SpinnerColumn, TextColumn
from rich.table import Table

from proyecto_isabelle.parse import markdown
from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES, extract_thy_content
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.util import (
    ROOT_DIR,
    PROOFS_DIR,
    save_proof,
    sanitize_model_name,
)

app = typer.Typer(help="Batch process exercises with an LLM and verify with Isabelle")
console = Console()

DEFAULT_MODEL = "anthropic/claude-haiku-4-5-20251001"
DEFAULT_THINKING_BUDGET = 1024


def has_been_processed(exercise_path: Path, model: str) -> bool:
    """Check if an exercise has already been processed for a given model."""
    exercise_name = exercise_path.stem
    proof_dir = (
        PROOFS_DIR / f"exercise={exercise_name}" / f"model={sanitize_model_name(model)}"
    )
    if not proof_dir.exists():
        return False
    # Check if there are any .thy files in the directory
    return any(proof_dir.glob("*.thy"))


def process_exercise(
    exercise_path: Path,
    model: str,
    thinking_budget: int,
) -> dict[str, Any]:
    """Process a single exercise and return the results."""
    exercise = markdown.load_text(exercise_path)
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise)

    response = ask(
        prompt=prompt,
        model=model,
        temperature=1.0,  # Required for extended thinking
        max_tokens=4096,
        thinking_budget=thinking_budget,
    )

    result: dict[str, Any] = {
        "exercise_path": exercise_path,
        "model": model,
        "success": response.success,
    }

    if not response.success:
        result["error"] = response.error
        return result

    thy_content = extract_thy_content(response.content or "")
    if thy_content is None:
        result["error"] = "Failed to extract .thy content from response"
        return result

    # Verify with Isabelle
    isabelle_result = query_content(thy_content)
    result["verified"] = isabelle_result.verified
    result["isabelle_errors"] = isabelle_result.errors

    # Save the proof
    saved_path = save_proof(
        model=model,
        exercise_path=exercise_path,
        exercise=exercise,
        thy_content=thy_content,
        verified=isabelle_result.verified,
        errors=isabelle_result.errors,
        raw_response=response.content or "",
        thinking=response.thinking,
        thinking_budget=thinking_budget,
    )
    result["saved_path"] = saved_path

    return result


def get_exercises(exercises_dir: Path) -> list[Path]:
    """Get all exercise files from the given directory."""
    return sorted(exercises_dir.glob("*.md"))


def resolve_exercise_path(exercise: str, exercises_dir: Path) -> Path | None:
    """Resolve an exercise name or path to a full Path."""
    # If it's already a path that exists
    exercise_path = Path(exercise)
    if exercise_path.exists():
        return exercise_path

    # Try as absolute path from ROOT_DIR
    if (ROOT_DIR / exercise).exists():
        return ROOT_DIR / exercise

    # Try as name in exercises_dir (with or without .md)
    name = exercise if exercise.endswith(".md") else f"{exercise}.md"
    candidate = exercises_dir / name
    if candidate.exists():
        return candidate

    return None


@app.command()
def main(
    exercise: Annotated[
        str | None,
        typer.Option(help="Single exercise to process (name or path)"),
    ] = None,
    model: Annotated[
        str,
        typer.Option(help="Model to use for generating proofs"),
    ] = DEFAULT_MODEL,
    thinking_budget: Annotated[
        int,
        typer.Option(help="Thinking budget for extended thinking"),
    ] = DEFAULT_THINKING_BUDGET,
    limit: Annotated[
        int | None,
        typer.Option(help="Limit the number of exercises to process"),
    ] = None,
    shuffle: Annotated[
        bool,
        typer.Option(help="Shuffle the exercises before processing"),
    ] = False,
    seed: Annotated[
        int | None,
        typer.Option(help="Random seed for shuffling"),
    ] = None,
    force: Annotated[
        bool,
        typer.Option(help="Force re-processing of already processed exercises"),
    ] = False,
    exercises_dir: Annotated[
        str,
        typer.Option(help="Directory containing exercises (relative to project root)"),
    ] = "data/exercises",
) -> None:
    """Process exercises and verify proofs with Isabelle."""
    exercises_path = ROOT_DIR / exercises_dir

    # Handle single exercise mode
    if exercise is not None:
        exercise_path = resolve_exercise_path(exercise, exercises_path)
        if exercise_path is None:
            console.print(f"[red]Error:[/red] Exercise not found: {exercise}")
            raise typer.Exit(1)
        exercises = [exercise_path]
        console.print(f"Processing single exercise: [cyan]{exercise_path.name}[/cyan]")
    else:
        exercises = get_exercises(exercises_path)
        console.print(
            f"Found [bold]{len(exercises)}[/bold] exercises in {exercises_path}"
        )

    # Shuffle and limit only apply in batch mode
    if exercise is None:
        if shuffle:
            if seed is not None:
                random.seed(seed)
            random.shuffle(exercises)
            console.print(f"[dim]Shuffled exercises (seed: {seed})[/dim]")

        if limit is not None:
            exercises = exercises[:limit]
            console.print(f"[dim]Limited to {len(exercises)} exercises[/dim]")

    # Filter out already processed exercises (unless force is set)
    if not force:
        original_count = len(exercises)
        exercises = [ex for ex in exercises if not has_been_processed(ex, model)]
        skipped = original_count - len(exercises)
        if skipped > 0:
            console.print(
                f"[yellow]Skipping {skipped} already processed exercises[/yellow]"
            )

    console.print(
        f"Processing [bold]{len(exercises)}[/bold] exercises with model [cyan]{model}[/cyan]\n"
    )

    # Process each exercise
    results: list[dict[str, Any]] = []
    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        console=console,
    ) as progress:
        for i, exercise_path in enumerate(exercises, 1):
            task_id = progress.add_task(
                f"[{i}/{len(exercises)}] {exercise_path.name}",
                total=None,
            )

            result = process_exercise(
                exercise_path=exercise_path,
                model=model,
                thinking_budget=thinking_budget,
            )
            results.append(result)

            progress.remove_task(task_id)

            # Print result
            prefix = f"[{i}/{len(exercises)}]"
            if not result.get("success", False):
                console.print(f"{prefix} [red]LLM Error:[/red] {result.get('error')}")
            elif "error" in result:
                console.print(f"{prefix} [red]Error:[/red] {result['error']}")
            else:
                verified = result.get("verified", False)
                if verified:
                    console.print(
                        f"{prefix} [green]VERIFIED[/green] - {exercise_path.name}"
                    )
                else:
                    console.print(
                        f"{prefix} [red]NOT VERIFIED[/red] - {exercise_path.name}"
                    )
                    if result.get("isabelle_errors"):
                        for err in result["isabelle_errors"]:
                            console.print(f"    [dim]{err}[/dim]")

    # Summary table
    console.print()
    table = Table(title="Summary")
    table.add_column("Metric", style="cyan")
    table.add_column("Count", justify="right")

    successful = [r for r in results if r.get("success", False) and "error" not in r]
    verified = [r for r in successful if r.get("verified", False)]

    table.add_row("Total exercises processed", str(len(results)))
    table.add_row("Successfully processed", str(len(successful)))
    table.add_row("Verified by Isabelle", f"[green]{len(verified)}[/green]")
    table.add_row(
        "Verification rate",
        f"{len(verified) / len(successful) * 100:.1f}%" if successful else "N/A",
    )

    console.print(table)


if __name__ == "__main__":
    app()
