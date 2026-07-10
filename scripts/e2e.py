from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES, extract_thy_content
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.util import save_proof
from proyecto_isabelle.sync.repository import SupabaseRepository


def main(name="bolzano", model_name="anthropic/claude-sonnet-4-5-20250929") -> None:
    repo = SupabaseRepository()

    exercise = repo.read_as_exercise(name)
    exercise_statement = exercise.statement

    # Create the prompt
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise_statement)

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

    # Save the proof
    save_proof(
        model=model,
        exercise=exercise_statement,
        thy_content=thy_content,
        verified=result.verified,
        errors=result.errors,
        raw_response=response.content or "",
        thinking=response.thinking,
        thinking_budget=thinking_budget,
    )


if __name__ == "__main__":
    main()
