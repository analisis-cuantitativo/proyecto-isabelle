"""CLI for uploading local data to GCP Cloud Storage bucket."""

from typing import Annotated, Optional

import typer
from rich.console import Console

from proyecto_isabelle.sync import SYNC_DIRS, GCSClient, upload_to_gcs

app = typer.Typer(help="Upload local data to GCP Cloud Storage bucket.")
console = Console()


@app.command()
def main(
    subdir: Annotated[
        Optional[str],
        typer.Option(
            "--subdir",
            "-s",
            help=f"Subdirectory to upload ({', '.join(SYNC_DIRS)}). Default: all.",
        ),
    ] = None,
    dry_run: Annotated[
        bool,
        typer.Option("--dry-run", "-n", help="Preview operations without executing."),
    ] = False,
    verbose: Annotated[
        bool,
        typer.Option("--verbose", "-v", help="Print detailed progress."),
    ] = False,
) -> None:
    """Upload local data to GCP Cloud Storage bucket with incremental sync."""
    # Validate subdir if provided
    if subdir is not None and subdir not in SYNC_DIRS:
        console.print(f"[red]Invalid subdir: {subdir}[/red]")
        console.print(f"[dim]Valid options: {', '.join(SYNC_DIRS)}[/dim]")
        raise typer.Exit(1)

    if dry_run:
        console.print("[yellow]Dry run mode - no changes will be made[/yellow]\n")

    # Create client
    try:
        client = GCSClient()
        console.print(f"[bold]Bucket:[/bold] {client.bucket_name}")
    except ValueError as e:
        console.print(f"[red]{e}[/red]")
        raise typer.Exit(1)

    # Run upload
    scope = subdir if subdir else "all directories"
    console.print(f"[bold]Uploading:[/bold] {scope}\n")

    with console.status("[bold green]Uploading files...") if not verbose else console:
        result = upload_to_gcs(
            client=client,
            subdir=subdir,
            dry_run=dry_run,
            verbose=verbose,
            console=console,
        )

    # Print summary
    console.print()
    if dry_run:
        console.print(f"[cyan]Would upload: {result.uploaded} files[/cyan]")
    else:
        console.print(f"[green]Uploaded: {result.uploaded} files[/green]")
    console.print(f"[dim]Skipped (unchanged): {result.skipped} files[/dim]")

    if result.errors:
        console.print(f"[red]Errors: {len(result.errors)}[/red]")
        raise typer.Exit(1)


if __name__ == "__main__":
    app()
