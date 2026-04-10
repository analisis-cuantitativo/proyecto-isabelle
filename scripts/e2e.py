"""
One end-to-end example in which we ask an LLM to prove a theorem.
"""

import json
from datetime import datetime, timezone
from pathlib import Path

from proyecto_isabelle.parse import thy, markdown
from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES, extract_thy_content
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.util import generate_hash, sanitize_model_name

PROOFS_DIR = Path(__file__).parent.parent / "data" / "proofs"


def save_proof(
    model: str,
    exercise_path: Path,
    exercise: str,
    thy_content: str,
    verified: bool,
    errors: list[str],
    raw_response: str,
    thinking: str | None = None,
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
        "thinking": thinking,
    }
    meta_path = proof_dir / f"{proof_hash}.json"
    meta_path.write_text(json.dumps(metadata, indent=2))

    return thy_path


def main() -> None:
    # Load the exercise
    exercise_path = (
        Path(__file__).parent.parent / "data" / "raw" / "exercises" / "injectivity.md"
    )
    exercise = markdown.load_text(exercise_path)
    print(f"Loaded exercise:\n{exercise}\n")

    # Create the prompt
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise)

    # Query the LLM (using Claude Sonnet with extended thinking)
    model = "anthropic/claude-sonnet-4-5-20250929"
    thinking_budget = 10000
    print(f"Querying {model} with thinking_budget={thinking_budget}...")
    response = ask(
        prompt=prompt,
        model=model,
        temperature=1.0,  # Required for extended thinking
        max_tokens=16000,  # Must be > thinking_budget
        thinking_budget=thinking_budget,
    )

    if not response.success:
        print(f"LLM query failed: {response.error}")
        return

    print(f"LLM response received (tokens used: {response.usage})\n")
    if response.thinking:
        print(f"Thinking:\n{response.thinking}\n")
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
        thinking=response.thinking,
    )
    print(f"\nProof saved to: {saved_path}")


if __name__ == "__main__":
    main()
