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
    llm_response: LLMResponse,
    isabelle_response: IsabelleResponse,
    prompt: str,
    thy_response: thy,
) -> Path:
    """Save the proof and metadata to disk."""
    timestamp = datetime.now(timezone.utc).isoformat()
    proof_hash = generate_hash(exercise.proposed_thy_code, timestamp)

    # Create exercise/model directory structure
    proof_dir = (
        PROOFS_DIR
        / f"exercise={exercise.name}"
        / f"model={sanitize_model_name(llm_response.model)}"
    )
    proof_dir.mkdir(parents=True, exist_ok=True)

    # Save the .thy file
    thy_path = proof_dir / f"{proof_hash}.thy"
    thy.save_text(thy_response or "", thy_path)

    # Save thinking to separate file if present
    if llm_response.thinking:
        thinking_path = proof_dir / f"{proof_hash}.thinking.md"
        try:
            thinking_path.write_text(llm_response.thinking)
        except UnicodeEncodeError as e:
            print(f"Couldn't save the thinking thread {llm_response.thinking}.\n\n{e}")

    # Save metadata as JSON (without thinking content to avoid duplication)
    metadata = {
        "exercise_id": exercise.id,
        "model_name": llm_response.model,
        "was_given_the_correct_thy_statement": prompt,
        "thy_results": thy_response,
        "thoughts": llm_response.thinking,
        "tokens_consumed": llm_response.usage.total_tokens,
        "num_of_passes": llm_response,
        "max_num_of_passes": prompt,
        "correctly_verified": isabelle_response.verified,
        "deepisahol_metadata": isabelle_response,
    }
    meta_path = proof_dir / f"{proof_hash}.json"
    meta_path.write_text(json.dumps(metadata, indent=2))

    return thy_path
