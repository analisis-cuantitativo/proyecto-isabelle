from proyecto_isabelle.query.isabelle import query_content, IsabelleResponse
from proyecto_isabelle.query.llm import ask, LLMResponse
from proyecto_isabelle.util import save_proof
from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.prompts import extract_thy_content


def run_agent(
    prompt: str,
    model_name: str = "anthropic/claude-sonnet-4-5-20250929",
) -> tuple[LLMResponse, IsabelleResponse]:
    # Query the LLM (using Claude Sonnet with extended thinking)

    model = model_name
    max_tokens = 4096 * 4
    thinking_budget = max_tokens // 4
    print(f"Querying {model} with thinking_budget={thinking_budget}...")
    response = ask(
        prompt=prompt,
        model=model,
        temperature=1.0,  # Required for extended thinking
        max_tokens=max_tokens,  # Must be > thinking_budget
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

    return response, result


def save_proof_result(
    exercise: Exercise,
    agents_response: tuple[LLMResponse, IsabelleResponse],
    prompt: str,
) -> None:
    repo = SupabaseRepository()

    llm_response, isabelle_response = agents_response[0], agents_response[1]
    thy = extract_thy_content(llm_response.content)

    # Save the proof
    save_proof(
        exercise=exercise,
        llm_response=llm_response,
        isabelle_response=isabelle_response,
        prompt=prompt,
        thy=thy,
    )

    repo.save_online(
        exercise=exercise,
        llm_response=llm_response,
        isabelle_response=isabelle_response,
        prompt=prompt,
        thy=thy,
    )
