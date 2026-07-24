import json
from datetime import datetime, timezone
from pathlib import Path

from proyecto_isabelle.parse import thy
from proyecto_isabelle.util import generate_hash, sanitize_model_name, PROOFS_DIR

from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.query.llm import LLMResponse
from proyecto_isabelle.query.isabelle import IsabelleResponse


def save_proof(
    exercise: Exercise,
    LLMResponse: LLMResponse,
    IsabelleResponse: IsabelleResponse,
    prompt: str,
) -> Path:
    """Save the proof and metadata to disk."""
    timestamp = datetime.now(timezone.utc).isoformat()
    proof_hash = generate_hash(exercise.proposed_thy_code, timestamp)

    # Create exercise/model directory structure
    proof_dir = (
        PROOFS_DIR
        / f"exercise={exercise.name}"
        / f"model={sanitize_model_name(LLMResponse.model)}"
    )
    proof_dir.mkdir(parents=True, exist_ok=True)

    # Save the .thy file
    thy_path = proof_dir / f"{proof_hash}.thy"
    thy.save_text(LLMResponse.content or "", thy_path)  # IsabelleResponse.state

    # Save thinking to separate file if present
    if LLMResponse.thinking:
        thinking_path = proof_dir / f"{proof_hash}.thinking.md"
        try:
            thinking_path.write_text(LLMResponse.thinking)
        except UnicodeEncodeError as e:
            print(f"Couldn't save the thinking thread {LLMResponse.thinking}.\n\n{e}")

    # Save metadata as JSON (without thinking content to avoid duplication)
    metadata = {
        "exercise_id": exercise.id,
        "model_name": LLMResponse.model,
        "was_given_the_correct_thy_statement": prompt,
        "thy_results": LLMResponse.content,  # IsabelleResponse.state
        "thoughts": LLMResponse.thinking,
        "tokens_consumed": LLMResponse.usage.total_tokens,
        "num_of_passes": LLMResponse,
        "max_num_of_passes": prompt,
        "correctly_verified": IsabelleResponse.verified,
        "deepisahol_metadata": IsabelleResponse,
        # "created_at":,
    }
    meta_path = proof_dir / f"{proof_hash}.json"
    meta_path.write_text(json.dumps(metadata, indent=2))

    return thy_path
