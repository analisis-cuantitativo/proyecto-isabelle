from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES
from proyecto_isabelle.query.agent import run_agent
from proyecto_isabelle.sync.repository import SupabaseRepository


def main(
    name: str = "bolzano", model_name: str = "anthropic/claude-sonnet-4-5-20250929"
) -> None:
    repo = SupabaseRepository()

    exercise = repo.read_as_exercise(name)
    exercise_statement = exercise.statement

    # Create the prompt
    prompt = PROMPT_FOR_EXERCISES.format(exercise=exercise_statement)

    run_agent(exercise, prompt, model_name)


if __name__ == "__main__":
    main()
