import json
import logging
from datetime import datetime, timezone
from pathlib import Path

from proyecto_isabelle.parse import thy
from proyecto_isabelle.prompts import extract_thy_content
from proyecto_isabelle.util import generate_hash, sanitize_model_name, PROOFS_DIR

from proyecto_isabelle.sync.models import Benchmark, Exercise
from proyecto_isabelle.query.llm import LLMResponse
from proyecto_isabelle.query.isabelle import IsabelleResponse

logger = logging.getLogger(__name__)


def to_benchmark(
    exercise: Exercise,
    llm_response: LLMResponse,
    isabelle_response: IsabelleResponse,
    prompt: str | None,
    thy_response: str | None,
    num_of_passes: int = 1,
    max_num_of_passes: int = 3,
) -> Benchmark:
    """Build a validated ``Benchmark`` row from a single agent pass.

    ``pydantic`` validates every field, so a wrong type here fails loudly
    instead of silently reaching the database or the metadata file.
    """
    if exercise.id is None:
        raise ValueError("Exercise needs an id to be turned into a Benchmark row.")

    was_given_the_correct_thy_statement = False
    if exercise.corrected_thy_code is not None:
        thy_code_in_prompt = extract_thy_content(prompt or "")
        was_given_the_correct_thy_statement = (
            thy_code_in_prompt == exercise.corrected_thy_code
        )

    return Benchmark(
        exercise_id=exercise.id,
        model_name=llm_response.model or "",
        was_given_the_correct_thy_statement=was_given_the_correct_thy_statement,
        thy_results=[thy_response or ""],
        thoughts=[llm_response.thinking],
        tokens_consumed=(llm_response.usage.total_tokens if llm_response.usage else 0),
        num_of_passes=num_of_passes,
        max_num_of_passes=max_num_of_passes,
        correctly_verified=isabelle_response.verified,
        deepisahol_metadata=[isabelle_response.model_dump()],
    )


def save_proof(
    exercise: Exercise,
    llm_response: LLMResponse,
    isabelle_response: IsabelleResponse,
    prompt: str | None,
    thy_response: str | None,
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
            logger.warning(
                "Couldn't save the thinking thread %s.\n\n%s",
                llm_response.thinking,
                e,
            )

    # Save metadata as a validated Benchmark row
    benchmark = to_benchmark(
        exercise=exercise,
        llm_response=llm_response,
        isabelle_response=isabelle_response,
        prompt=prompt,
        thy_response=thy_response,
    )
    meta_path = proof_dir / f"{proof_hash}.json"
    meta_path.write_text(json.dumps(benchmark.model_dump(mode="json"), indent=2))

    return thy_path
