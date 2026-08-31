import logging

from proyecto_isabelle.query.isabelle import query_content, IsabelleResponse
from proyecto_isabelle.query.llm import ask, LLMResponse
from proyecto_isabelle.util import save_proof
from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.prompts import extract_thy_content

logger = logging.getLogger(__name__)


def run_agent(
    prompt: str,
    model_name: str = "anthropic/claude-sonnet-4-5-20250929",
) -> tuple[LLMResponse, IsabelleResponse] | None:
    # Query the LLM (using Claude Sonnet with extended thinking)
    model = model_name
    max_tokens = 4096 * 4
    thinking_budget = max_tokens // 4
    logger.info("Querying %s with thinking_budget=%s...", model, thinking_budget)
    response = ask(
        prompt=prompt,
        model=model,
        temperature=1.0,  # Required for extended thinking
        max_tokens=max_tokens,  # Must be > thinking_budget
        thinking_budget=thinking_budget,
    )

    if not response.success:
        logger.error("LLM query failed: %s", response.error)
        return

    logger.info("LLM response received (tokens used: %s)", response.usage)
    if response.thinking:
        logger.debug("Thinking:\n%s", response.thinking)
    logger.debug("Raw response:\n%s", response.content)

    # Extract the .thy content
    thy_content = extract_thy_content(response.content or "")
    if thy_content is None:
        logger.error("Failed to extract .thy content from response")
        return

    logger.debug("Extracted .thy content:\n%s", thy_content)

    # Query Isabelle for verification
    logger.info("Verifying with Isabelle...")
    result = query_content(thy_content)

    logger.info(
        "Isabelle verification result: success=%s verified=%s message=%s",
        result.success,
        result.verified,
        result.message,
    )
    if result.errors:
        logger.error("Isabelle errors: %s", result.errors)

    return response, result


def save_proof_result(
    exercise: Exercise,
    agents_response: tuple[LLMResponse, IsabelleResponse],
    prompt: str,
) -> None:
    repo = SupabaseRepository()

    llm_response, isabelle_response = agents_response
    thy = extract_thy_content(llm_response.content or "")

    # Save the proof
    save_proof(
        exercise=exercise,
        llm_response=llm_response,
        isabelle_response=isabelle_response,
        prompt=prompt,
        thy_response=thy,
    )

    repo.save_online(
        exercise=exercise,
        llm_response=llm_response,
        isabelle_response=isabelle_response,
        prompt=prompt,
        thy_response=thy,
    )
