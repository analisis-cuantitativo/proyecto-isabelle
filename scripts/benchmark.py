from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES
from proyecto_isabelle.query.agent import run_agent
from proyecto_isabelle.sync.repository import SupabaseRepository


def model_benchmark(model_name: str, dry_run: bool = True, proof: bool = False) -> None:
    repo = SupabaseRepository()

    exercises = repo.get_missing_exercises_by_model(model_name)

    for exercise in exercises:
        if dry_run:
            print(f"Processing exercise: {exercise.name}")
        else:
            prompt = (
                None
                if proof
                else PROMPT_FOR_EXERCISES.format(exercise=exercise.statement)
            )

            run_agent(prompt, model_name)


# def model_benchmark_for_exercise(exercise_id: int, model_name: str) -> None:
