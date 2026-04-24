"""CLI for formalizing mathematical exercises using LLMs and Isabelle."""

from pathlib import Path
from typing import Annotated, Optional

import click
import typer
from rich.console import Console
from rich.panel import Panel

from proyecto_isabelle.parse import markdown
from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES, extract_thy_content
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.util import save_proof
from proyecto_isabelle.util.constants import MODELS

app = typer.Typer(help="Formalize mathematical exercises using LLMs and Isabelle.")
console = Console()

DEFAULT_MODEL = "anthropic/claude-sonnet-4-5-20250929"


@app.command()
def main(
    exercise_path: Annotated[
        Optional[Path],
        typer.Option("--file", "-f", help="Path to the exercise markdown file"),
    ] = None,
    exercise_text: Annotated[
        Optional[str],
        typer.Option("--text", "-e", help="Exercise text (theorem to prove)"),
    ] = None,
    exercise_name: Annotated[
        Optional[str],
        typer.Option("--name", "-n", help="Exercise name (required when using --text)"),
    ] = None,
    model: Annotated[
        str,
        typer.Option(
            "--model", "-m", help="LLM model to use", click_type=click.Choice(MODELS)
        ),
    ] = DEFAULT_MODEL,
    max_tokens: Annotated[
        int,
        typer.Option("--max-tokens", "-t", help="Maximum tokens for LLM response"),
    ] = 4096 * 4,
    thinking_budget: Annotated[
        Optional[int],
        typer.Option(
            "--thinking-budget",
            "-b",
            help="Token budget for extended thinking (defaults to max_tokens // 4)",
        ),
    ] = None,
    no_save: Annotated[
        bool,
        typer.Option("--no-save", help="Don't save the proof to disk"),
    ] = False,
) -> None:
    """Formalize a mathematical exercise by querying an LLM and verifying with Isabelle."""
    # Validate that exactly one of exercise_path or exercise_text is provided
    if exercise_path is None and exercise_text is None:
        console.print("[red]Either --file or --text must be provided[/red]")
        raise typer.Exit(1)

    if exercise_path is not None and exercise_text is not None:
        console.print("[red]Cannot use both --file and --text[/red]")
        raise typer.Exit(1)

    # Validate that --name is provided when using --text
    if exercise_text is not None and exercise_name is None:
        console.print("[red]--name is required when using --text[/red]")
        raise typer.Exit(1)

    # Load the exercise
    if exercise_path is not None:
        if not exercise_path.is_absolute():
            exercise_path = Path.cwd() / exercise_path

        if not exercise_path.exists():
            console.print(f"[red]Exercise file not found: {exercise_path}[/red]")
            raise typer.Exit(1)

        exercise = markdown.load_text(exercise_path)
        resolved_exercise_path = exercise_path
    else:
        assert exercise_text is not None  # Validated above
        assert exercise_name is not None  # Validated above
        exercise = exercise_text
        # Create a synthetic path for saving purposes
        resolved_exercise_path = Path(f"{exercise_name}.md")

    console.print(Panel(exercise, title="Exercise", border_style="blue"))

    # Create the prompt
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise)

    # Determine thinking budget
    actual_thinking_budget = (
        thinking_budget if thinking_budget is not None else max_tokens // 4
    )

    # Query the LLM
    console.print(
        f"\n[bold]Querying[/bold] [cyan]{model}[/cyan] "
        f"(thinking_budget={actual_thinking_budget})..."
    )

    with console.status("[bold green]Waiting for LLM response..."):
        response = ask(
            prompt=prompt,
            model=model,
            temperature=1.0,
            max_tokens=max_tokens,
            thinking_budget=actual_thinking_budget,
        )

    if not response.success:
        console.print(f"[red]LLM query failed: {response.error}[/red]")
        raise typer.Exit(1)

    console.print(f"[green]LLM response received[/green] (tokens: {response.usage})\n")

    if response.thinking:
        console.print(Panel(response.thinking, title="Thinking", border_style="yellow"))

    console.print(
        Panel(response.content or "", title="Raw Response", border_style="blue")
    )

    # Extract the .thy content
    thy_content = extract_thy_content(response.content or "")
    if thy_content is None:
        console.print("[red]Failed to extract .thy content from response[/red]")
        raise typer.Exit(1)

    console.print(
        Panel(thy_content, title="Extracted .thy Content", border_style="green")
    )

    # Query Isabelle for verification
    console.print("\n[bold]Verifying with Isabelle...[/bold]")
    with console.status("[bold green]Running Isabelle verification..."):
        result = query_content(thy_content)

    # Display results
    if result.verified:
        console.print("[bold green]Verification successful![/bold green]")
    else:
        console.print("[bold red]Verification failed[/bold red]")

    console.print(f"  Success: {result.success}")
    console.print(f"  Verified: {result.verified}")
    console.print(f"  Message: {result.message}")
    if result.errors:
        console.print(f"  [red]Errors: {result.errors}[/red]")

    # Save the proof
    if not no_save:
        saved_path = save_proof(
            model=model,
            exercise_path=resolved_exercise_path,
            exercise=exercise,
            thy_content=thy_content,
            verified=result.verified,
            errors=result.errors,
            raw_response=response.content or "",
            thinking=response.thinking,
            thinking_budget=actual_thinking_budget,
        )
        console.print(f"\n[bold]Proof saved to:[/bold] {saved_path}")
    else:
        console.print("\n[dim]Proof not saved (--no-save flag)[/dim]")


if __name__ == "__main__":
    app()
