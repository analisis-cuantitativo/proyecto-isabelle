import typer
from rich.console import Console
from rich.panel import Panel
from rich.syntax import Syntax

from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.prompts import (
    PROMPT_FOR_THY_CONTENT_PROPOSAL,
    extract_thy_content,
)
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.sync.repository import SupabaseRepository

app = typer.Typer()
console = Console()

MODEL = "anthropic/claude-opus-4-6"
MAX_TOKENS = 4096 * 6
MAX_RETRIES = 3


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

        if not response.success:
            console.print(
                Panel(
                    f"[red]LLM request failed[/red]\n{response.error or 'Unknown error'}",
                    title="Error",
                    border_style="red",
                )
            )
            continue

        if response.thinking:
            console.print(
                Panel(
                    response.thinking,
                    title="Thinking",
                    border_style="dim",
                )
            )

        thy_content = extract_thy_content(response.content or "")
        if thy_content is None:
            console.print(
                Panel(
                    "[red]Failed to extract thy content from response[/red]",
                    title="Extraction Error",
                    border_style="red",
                )
            )
            continue

        console.print(
            Panel(
                Syntax(thy_content, "isabelle", theme="monokai"),
                title="Extracted Thy Content",
                border_style="green",
            )
        )

        isabelle_result = query_content(thy_content)

        if not isabelle_result.verified:
            console.print(
                Panel(
                    f"[red]Isabelle verification failed[/red]\n{isabelle_result.errors or 'Unknown error'}",
                    title="Verification Error",
                    border_style="red",
                )
            )
            continue

        console.print("[green]Verification successful![/green]")
        return exercise.model_copy(update={"proposed_thy_code": thy_content})

    console.print(
        Panel(
            f"[red]Failed to generate valid thy content after {MAX_RETRIES} attempts[/red]",
            title="Max Retries Exceeded",
            border_style="red",
        )
    )
    raise typer.Exit(code=1)


@app.command()
def run(exercise_name: str) -> None:
    repo = SupabaseRepository()
    exercise = repo.read_as_exercise(exercise_name)
    new_exercise = populate_proposed_thy_for_exercise(exercise)
    repo.write(new_exercise)
    console.print(f"[green]Successfully updated exercise: {exercise_name}[/green]")


@app.command()
def run_all() -> None:
    repo = SupabaseRepository()
    all_exercises = repo.read_with_empty_proposed_thy()

    if not all_exercises:
        console.print("[yellow]No exercises with empty proposed thy found[/yellow]")
        return

    console.print(f"[blue]Found {len(all_exercises)} exercises to process[/blue]")

    successful = 0
    failed = 0

    for i, exercise in enumerate(all_exercises, 1):
        console.print(f"\n[dim]({i}/{len(all_exercises)})[/dim]")
        try:
            new_exercise = populate_proposed_thy_for_exercise(exercise)
            repo.write(new_exercise)
            successful += 1
        except typer.Exit:
            failed += 1
            console.print(f"[red]Skipping exercise: {exercise.name}[/red]")

    console.print(
        Panel(
            f"[green]Successful: {successful}[/green]\n[red]Failed: {failed}[/red]",
            title="Summary",
            border_style="blue",
        )
    )


if __name__ == "__main__":
    app()
