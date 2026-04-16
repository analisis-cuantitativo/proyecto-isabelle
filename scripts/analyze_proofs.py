"""Example script showing how to analyze proof data."""

import pandas as pd
from rich.console import Console
from rich.table import Table

from proyecto_isabelle.analysis.load import (
    load_proofs,
    success_rate_by_exercise,
    success_rate_by_model,
    success_rate_by_model_and_exercise,
)

console = Console()


def df_to_table(df: pd.DataFrame, title: str) -> Table:
    table = Table(title=title)
    for col in df.columns:
        table.add_column(col)
    for _, row in df.iterrows():
        table.add_row(*[str(v) for v in row])
    return table


def main():
    df = load_proofs()
    console.print(f"[bold]Total proofs:[/bold] {len(df)}\n")

    console.print(df_to_table(success_rate_by_model(df), "Success Rate by Model"))
    console.print()
    console.print(df_to_table(success_rate_by_exercise(df), "Success Rate by Exercise"))
    console.print()
    console.print(
        df_to_table(
            success_rate_by_model_and_exercise(df), "Success Rate by Model and Exercise"
        )
    )


if __name__ == "__main__":
    main()
