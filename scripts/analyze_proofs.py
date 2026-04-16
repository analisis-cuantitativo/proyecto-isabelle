"""CLI for analyzing proof data."""

from typing import Annotated, Optional

import pandas as pd
import typer
from rich.console import Console
from rich.table import Table

from proyecto_isabelle.analysis.load import (
    load_proofs,
    success_rate_by_exercise,
    success_rate_by_model,
    success_rate_by_model_and_exercise,
)

app = typer.Typer(help="Analyze proof verification results.")
console = Console()


def df_to_table(df: pd.DataFrame, title: str) -> Table:
    table = Table(title=title)
    for col in df.columns:
        table.add_column(col)
    for _, row in df.iterrows():
        table.add_row(*[str(v) for v in row])
    return table


@app.command()
def main(
    exercise: Annotated[
        Optional[str],
        typer.Argument(help="Filter by exercise name"),
    ] = None,
):
    """Show proof verification statistics."""
    df = load_proofs()

    if exercise:
        df = df[df["exercise"] == exercise]
        if df.empty:
            console.print(f"[red]No proofs found for exercise: {exercise}[/red]")
            raise typer.Exit(1)
        console.print(f"[bold]Exercise:[/bold] {exercise}")
        console.print(f"[bold]Total proofs:[/bold] {len(df)}\n")
        console.print(df_to_table(success_rate_by_model(df), "Success Rate by Model"))
    else:
        console.print(f"[bold]Total proofs:[/bold] {len(df)}\n")
        console.print(df_to_table(success_rate_by_model(df), "Success Rate by Model"))
        console.print()
        console.print(
            df_to_table(success_rate_by_exercise(df), "Success Rate by Exercise")
        )
        console.print()
        console.print(
            df_to_table(
                success_rate_by_model_and_exercise(df),
                "Success Rate by Model and Exercise",
            )
        )


if __name__ == "__main__":
    app()
