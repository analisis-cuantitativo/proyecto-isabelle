"""Upload and download operations for GCS sync with MD5-based incremental sync."""

import json
from pathlib import Path

from dataclasses import dataclass

from rich.console import Console

from proyecto_isabelle.sync.client import GCSClient
from proyecto_isabelle.sync.hash import compute_md5
from proyecto_isabelle.util.constants import ROOT_DIR

# Imports for integration with the database
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.sync.models import Exercise

# Directories to sync
SYNC_DIRS = ["exercises", "exercises_with_proof", "proofs"]

# Base data directory
DATA_DIR = ROOT_DIR / "data"


@dataclass
class SyncResult:
    """Result of a sync operation."""

    uploaded: int = 0
    downloaded: int = 0
    skipped: int = 0
    errors: list[str] | None = None

    def __post_init__(self) -> None:
        if self.errors is None:
            self.errors = []


def upload_to_gcs(
    client: GCSClient,
    subdir: str | None = None,
    dry_run: bool = False,
    verbose: bool = False,
    console: Console | None = None,
) -> SyncResult:
    """Upload local data to GCS bucket with MD5-based incremental sync.

    Args:
        client: GCSClient instance.
        subdir: Optional subdirectory to sync (e.g., "proofs"). If None, syncs all.
        dry_run: If True, only preview operations without executing.
        verbose: If True, print detailed progress.
        console: Rich console for output.

    Returns:
        SyncResult with counts of uploaded, skipped, and errors.
    """
    if console is None:
        console = Console()

    result = SyncResult()
    dirs_to_sync = [subdir] if subdir else SYNC_DIRS

    for sync_dir in dirs_to_sync:
        local_dir = DATA_DIR / sync_dir
        if not local_dir.exists():
            if verbose:
                console.print(f"[yellow]Skipping {sync_dir}/ (not found)[/yellow]")
            continue

        # Find all files in the directory
        for local_path in local_dir.rglob("*"):
            if local_path.is_dir():
                continue

            # Compute blob name (relative path from data/)
            blob_name = str(local_path.relative_to(DATA_DIR))

            # Get local MD5
            local_md5 = compute_md5(local_path)

            # Check if blob exists and compare MD5
            blob = client.blob(blob_name)
            try:
                blob.reload()
                remote_md5 = blob.md5_hash
                if local_md5 == remote_md5:
                    if verbose:
                        console.print(f"[dim]Skip (unchanged): {blob_name}[/dim]")
                    result.skipped += 1
                    continue
            except Exception:
                # Blob doesn't exist, will upload
                pass

            # Upload the file
            if dry_run:
                console.print(f"[cyan]Would upload: {blob_name}[/cyan]")
                result.uploaded += 1
            else:
                try:
                    blob.upload_from_filename(str(local_path))
                    if verbose:
                        console.print(f"[green]Uploaded: {blob_name}[/green]")
                    result.uploaded += 1
                except Exception as e:
                    error_msg = f"Error uploading {blob_name}: {e}"
                    console.print(f"[red]{error_msg}[/red]")
                    result.errors.append(error_msg)

    return result


def download_from_gcs(
    client: GCSClient,
    subdir: str | None = None,
    dry_run: bool = False,
    verbose: bool = False,
    console: Console | None = None,
) -> SyncResult:
    """Download data from GCS bucket to local with MD5-based incremental sync.

    Args:
        client: GCSClient instance.
        subdir: Optional subdirectory to sync (e.g., "proofs"). If None, syncs all.
        dry_run: If True, only preview operations without executing.
        verbose: If True, print detailed progress.
        console: Rich console for output.

    Returns:
        SyncResult with counts of downloaded, skipped, and errors.
    """
    if console is None:
        console = Console()

    result = SyncResult()
    prefixes = [subdir] if subdir else SYNC_DIRS

    for prefix in prefixes:
        # List all blobs with this prefix
        blobs = client.list_blobs(prefix=prefix)

        for blob in blobs:
            # Skip "directory" blobs (ending with /)
            if blob.name.endswith("/"):
                continue

            local_path = DATA_DIR / blob.name

            # Check if local file exists and compare MD5
            if local_path.exists():
                local_md5 = compute_md5(local_path)
                if local_md5 == blob.md5_hash:
                    if verbose:
                        console.print(f"[dim]Skip (unchanged): {blob.name}[/dim]")
                    result.skipped += 1
                    continue

            # Download the file
            if dry_run:
                console.print(f"[cyan]Would download: {blob.name}[/cyan]")
                result.downloaded += 1
            else:
                try:
                    # Ensure parent directory exists
                    local_path.parent.mkdir(parents=True, exist_ok=True)
                    blob.download_to_filename(str(local_path))
                    if verbose:
                        console.print(f"[green]Downloaded: {blob.name}[/green]")
                    result.downloaded += 1
                except Exception as e:
                    error_msg = f"Error downloading {blob.name}: {e}"
                    console.print(f"[red]{error_msg}[/red]")
                    result.errors.append(error_msg)

    return result


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

    try:
        # 2. The repository uploads the data
        repo = SupabaseRepository()
        repo.write(exercise)
        if verbose:
            console.print(
                f"[green]Successfully uploaded '{exercise.name}' to Supabase.[/green]"
            )
        return True
    except Exception as e:
        console.print(f"[red]Error en BD para '{exercise.name}': {e}[/red]")
        return False
