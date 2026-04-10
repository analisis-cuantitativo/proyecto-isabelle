"""
One end-to-end example in which we ask an LLM to prove a theorem.
"""

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

from proyecto_isabelle.parse.markdown import load_text
from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask

PROOFS_DIR = Path(__file__).parent.parent / "data" / "proofs"


def extract_thy_content(response: str) -> str | None:
    """Extract the .thy file content from an LLM response.

    Looks for code blocks marked with ```isabelle or ``` and extracts the content.
    """
    # Try to match ```isabelle ... ``` first
    pattern = r"```(?:isabelle|thy)?\s*\n(.*?)\n```"
    match = re.search(pattern, response, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None


def sanitize_model_name(model: str) -> str:
    """Convert model name to a valid directory name."""
    return model.replace("/", "_").replace(":", "_")


def generate_proof_hash(thy_content: str, timestamp: str) -> str:
    """Generate a short hash for the proof based on content and timestamp."""
    combined = f"{thy_content}{timestamp}"
    return hashlib.sha256(combined.encode()).hexdigest()[:12]


def save_proof(
    model: str,
    exercise_path: Path,
    exercise: str,
    thy_content: str,
    verified: bool,
    errors: list[str],
    raw_response: str,
) -> Path:
    """Save the proof and metadata to disk."""
    timestamp = datetime.now(timezone.utc).isoformat()
    proof_hash = generate_proof_hash(thy_content, timestamp)

    # Create exercise/model directory structure
    exercise_name = exercise_path.stem
    proof_dir = (
        PROOFS_DIR / f"exercise={exercise_name}" / f"model={sanitize_model_name(model)}"
    )
    proof_dir.mkdir(parents=True, exist_ok=True)

    # Save the .thy file
    thy_path = proof_dir / f"{proof_hash}.thy"
    thy_path.write_text(thy_content)

    # Save metadata as JSON
    metadata = {
        "hash": proof_hash,
        "model": model,
        "timestamp": timestamp,
        "exercise_path": str(exercise_path),
        "exercise": exercise,
        "verified": verified,
        "errors": errors,
        "raw_response": raw_response,
    }
    meta_path = proof_dir / f"{proof_hash}.json"
    meta_path.write_text(json.dumps(metadata, indent=2))

    return thy_path


def main() -> None:
    # Load the exercise
    exercise_path = Path(__file__).parent.parent / "data/raw/exercises/injectivity.md"
    exercise = load_text(exercise_path)
    print(f"Loaded exercise:\n{exercise}\n")

    # Create the prompt
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise)

    # Query the LLM (using Claude Sonnet)
    model = "anthropic/claude-sonnet-4-5-20250929"
    print(f"Querying {model}...")
    response = ask(
        prompt=prompt,
        model=model,
        temperature=0.0,
        max_tokens=4096,
    )

    if not response.success:
        print(f"LLM query failed: {response.error}")
        return

    print(f"LLM response received (tokens used: {response.usage})\n")
    print(f"Raw response:\n{response.content}\n")

    # Extract the .thy content
    thy_content = extract_thy_content(response.content or "")
    if thy_content is None:
        print("Failed to extract .thy content from response")
        return

    print(f"Extracted .thy content:\n{thy_content}\n")

    # Query Isabelle for verification
    print("Verifying with Isabelle...")
    result = query_content(thy_content)

    print("\nIsabelle verification result:")
    print(f"  Success: {result.success}")
    print(f"  Verified: {result.verified}")
    print(f"  Message: {result.message}")
    if result.errors:
        print(f"  Errors: {result.errors}")

    # Save the proof
    saved_path = save_proof(
        model=model,
        exercise_path=exercise_path,
        exercise=exercise,
        thy_content=thy_content,
        verified=result.verified,
        errors=result.errors,
        raw_response=response.content or "",
    )
    print(f"\nProof saved to: {saved_path}")


if __name__ == "__main__":
    main()
