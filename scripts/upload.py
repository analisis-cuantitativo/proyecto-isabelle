"""CLI for uploading local data to GCP Cloud Storage bucket or Database."""

from pathlib import Path
from typing import Annotated, Optional

import typer
from rich.console import Console

from proyecto_isabelle.sync import SYNC_DIRS, GCSClient, upload_to_gcs
from proyecto_isabelle.sync.operations import (
    load_exercise_from_path,
    upload_exercise_to_db,
)

app = typer.Typer(
    help="Upload local data to GCP Cloud Storage bucket or Supabase Database."
)
console = Console()


@app.command()
def main(
    subdir: Annotated[
        Optional[str],
        typer.Option(
            "--subdir",
            "-s",
            help=f"Subdirectory to upload to GCS ({', '.join(SYNC_DIRS)}). Default: all.",
        ),
    ] = None,
    path: Annotated[
        Optional[Path],
        typer.Option(
            "--path",
            "-p",
            help="Path to the exercise directory to upload to Database (contains .json and .md).",
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
    """Upload local data to GCP Cloud Storage bucket with incremental sync or Database"""

    if dry_run:
        console.print("[yellow]Dry run mode - no changes will be made[/yellow]\n")

    # If a path is provided, it is assumed that the data will be uploaded to the database,
    # ignoring the subdirectory for GCS

    if path is not None:
        if not path.is_dir():
            console.print(
                f"[red]Invalid path: '{path}' is not a valid directory.[/red]"
            )
            raise typer.Exit(1)

        if list(path.glob("*.json")):
            carpetas_a_procesar = [path]
        else:
            carpetas_a_procesar = [
                d for d in path.iterdir() if d.is_dir() and list(d.glob("*.json"))
            ]

        if not carpetas_a_procesar:
            console.print(
                f"[red]No se encontraron ejercicios (archivos .json y .md) en {path}.[/red]"
            )
            raise typer.Exit(1)

        console.print(
            f"[bold]Found {len(carpetas_a_procesar)} exercise(s) to upload from:[/bold] {path}\n"
        )

        with (
            console.status("[bold green]Uploading to Supabase...")
            if not verbose
            else console
        ):
            errores = 0
            for carpeta in carpetas_a_procesar:
                try:
                    exercise_obj = load_exercise_from_path(carpeta)

                    success = upload_exercise_to_db(
                        exercise=exercise_obj,
                        dry_run=dry_run,
                        verbose=verbose,
                        console=console,
                    )
                    if not success:
                        errores += 1
                except Exception as e:
                    console.print(
                        f"[red]Error procesando la carpeta {carpeta}: {e}[/red]"
                    )
                    errores += 1

        if errores > 0:
            console.print(
                f"[red]Finished with {errores} error(s). Review logs above.[/red]"
            )
            raise typer.Exit(1)

        console.print("[bold green]Database bulk upload complete.[/bold green]")
        return

    # If a database path was not provided,
    # we proceed to upload to GCS.

    # Validate subdir if provided
    if subdir is not None and subdir not in SYNC_DIRS:
        console.print(f"[red]Invalid subdir: {subdir}[/red]")
        console.print(f"[dim]Valid options: {', '.join(SYNC_DIRS)}[/dim]")
        raise typer.Exit(1)

    # Create client
    try:
        client = GCSClient()
        console.print(f"[bold]Bucket:[/bold] {client.bucket_name}")
    except ValueError as e:
        console.print(f"[red]{e}[/red]")
        raise typer.Exit(1)

    # Run upload
    scope = subdir if subdir else "all directories"
    console.print(f"[bold]Uploading to GCS:[/bold] {scope}\n")

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
