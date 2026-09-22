"""Build the offline benchmark analysis report.

Pulls every `benchmark` pass and exercise from Supabase, plus whatever local
`data/run_logs/*.jsonl` files are available, and writes a Markdown report
with figures to `data/analysis/reports/<timestamp>/report.md` covering:
exercise difficulty, per-topic model specialization, token consumption, and
common Isabelle failure modes. See `proyecto_isabelle.analysis` for the
underlying metrics.
"""

import typer

from proyecto_isabelle.analysis import build_report

app = typer.Typer()


@app.command()
def main(
    min_topic_attempts: int = typer.Option(
        1,
        help="Minimum (model, topic) attempts before it's included in the specialization breakdown.",
    ),
    version: int = typer.Option(
        0,
        help=(
            "Benchmark campaign to report on (0 = all campaigns pooled). "
            "Campaigns ran against different agent revisions, so a pooled "
            "report averages incomparable conditions -- pass 1 or 2."
        ),
    ),
) -> None:
    paths = build_report(
        min_topic_attempts=min_topic_attempts,
        version=version or None,
    )
    if not version:
        typer.echo(
            "Warning: reporting over all campaigns pooled; pass --version to "
            "scope to one."
        )
    typer.echo(f"Report written to {paths.report_md}")
    typer.echo(f"Figures written to {paths.figures}")


if __name__ == "__main__":
    app()
