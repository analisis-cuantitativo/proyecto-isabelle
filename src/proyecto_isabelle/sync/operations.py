"""Upload and download operations for GCS sync with MD5-based incremental sync."""

import json
from pathlib import Path

from rich.console import Console

from proyecto_isabelle.util.constants import ROOT_DIR

# Imports for integration with the database
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.sync.models import Exercise

# Directories to sync
SYNC_DIRS = ["exercises", "exercises_with_proof", "proofs"]

# Base data directory
DATA_DIR = ROOT_DIR / "data"


def parse_markdown_exercise(md_content: str) -> tuple[str, str]:
    """Extracts statement and proof by splitting at the proof environment."""
    parts = md_content.split(r"\begin{proof}")

    statement = parts[0].strip()
    proof = ""

    if len(parts) > 1:
        proof_content = parts[1]
        end_idx = proof_content.find(r"\end{proof}")

        if end_idx != -1:
            proof = proof_content[:end_idx].strip()
        else:
            proof = proof_content.strip()

    return statement, proof


def load_exercise_from_path(path: Path) -> Exercise:
    """Reads the local files from a directory and returns a validated Exercise object."""
    json_files = list(path.glob("*.json"))
    md_files = list(path.glob("*.md"))
    thy_files = list(path.glob("*.thy"))

    # We keep the previous logic of the mandatory .md and .json files.
    if not json_files or not md_files:
        raise FileNotFoundError(f"Required files (.json, .md) are missing in {path}")

    with open(json_files[0], "r", encoding="utf-8") as f:
        raw_data = json.load(f)

    with open(md_files[0], "r", encoding="utf-8") as f:
        statement, proof = parse_markdown_exercise(f.read())
        raw_data["statement"] = statement
        raw_data["proof"] = proof

    # solution to issue 35
    if thy_files:
        with open(thy_files[0], "r") as f:
            raw_data["proposed_thy_code"] = f.read()
    else:
        raw_data["proposed_thy_code"] = None

        console = Console()
        console.print(
            f"[yellow]Warning: No .thy file found in '{path.name}'"
            f"Uploading 'proposed_thy_code' as null[/yellow]"
        )

    # Pydantic validates that the data is perfect
    return Exercise(**raw_data)


def upload_exercise_to_db(
    exercise: Exercise,
    dry_run: bool = False,
    verbose: bool = False,
    console: Console | None = None,
) -> bool:
    """Uploads a validated Exercise object to the Supabase database"""
    if console is None:
        console = Console()

    if dry_run:
        console.print(f"[cyan]Would upload: '{exercise.name}' to Supabase[/cyan]")
        return True

    # 2. The repository uploads the data
    repo = SupabaseRepository()
    repo.write(exercise)
    if verbose:
        console.print(
            f"[green]Successfully uploaded '{exercise.name}' to Supabase.[/green]"
        )
    return True
