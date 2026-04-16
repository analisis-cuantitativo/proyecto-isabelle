"""
One end-to-end example in which we ask an LLM to prove a theorem.
"""

from proyecto_isabelle.parse import markdown
from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES, extract_thy_content
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm import ask
from proyecto_isabelle.util import ROOT_DIR, save_proof


def main() -> None:
    # Load the exercise
    exercise_path = ROOT_DIR / "data" / "exercises" / "injectivity.md"
    exercise = markdown.load_text(exercise_path)
    print(f"Loaded exercise:\n{exercise}\n")

    # Create the prompt
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise)

    # Query the LLM (using Claude Sonnet with extended thinking)
    model = "anthropic/claude-sonnet-4-5-20250929"
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
    saved_path = save_proof(
        model=model,
        exercise_path=exercise_path,
        exercise=exercise,
        thy_content=thy_content,
        verified=result.verified,
        errors=result.errors,
        raw_response=response.content or "",
        thinking=response.thinking,
        thinking_budget=thinking_budget,
    )
    print(f"\nProof saved to: {saved_path}")


if __name__ == "__main__":
    main()
