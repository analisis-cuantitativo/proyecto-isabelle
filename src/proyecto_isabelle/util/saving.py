import json
from datetime import datetime, timezone
from pathlib import Path

from proyecto_isabelle.parse import thy
from proyecto_isabelle.util import generate_hash, sanitize_model_name, PROOFS_DIR


def save_proof(
    model: str,
    exercise_path: Path,
    exercise: str,
    thy_content: str,
    verified: bool,
    errors: list[str],
    raw_response: str,
    thinking: str | None = None,
    thinking_budget: int | None = None,
) -> Path:
    """Save the proof and metadata to disk."""
    timestamp = datetime.now(timezone.utc).isoformat()
    proof_hash = generate_hash(thy_content, timestamp)

    # Create exercise/model directory structure
    exercise_name = exercise_path.stem
    proof_dir = (
        PROOFS_DIR / f"exercise={exercise_name}" / f"model={sanitize_model_name(model)}"
    )
    proof_dir.mkdir(parents=True, exist_ok=True)

    # Save the .thy file
    thy_path = proof_dir / f"{proof_hash}.thy"
    thy.save_text(thy_content, thy_path)

    # Save thinking to separate file if present
    if thinking:
        thinking_path = proof_dir / f"{proof_hash}.thinking.md"
        try:
            thinking_path.write_text(thinking)
        except UnicodeEncodeError as e:
            print(f"Couldn't save the thinking thread {thinking}.\n\n{e}")

    # Save metadata as JSON (without thinking content to avoid duplication)
    metadata = {
        "hash": proof_hash,
        "model": model,
        "timestamp": timestamp,
        "exercise_path": str(exercise_path),
        "exercise": exercise,
        "verified": verified,
        "errors": errors,
        "raw_response": raw_response,
        "thinking_budget": thinking_budget,
    }
    meta_path = proof_dir / f"{proof_hash}.json"
    meta_path.write_text(json.dumps(metadata, indent=2))

    return thy_path
