import typer
from proyecto_isabelle.prompts import PROMPT_FOR_EXERCISES
from proyecto_isabelle.query.agent import run_agent
from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.util.constants import Models

app = typer.Typer()


@app.command()
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


@app.command()
def benchmark(model: Models, exercise_name: str, include_proof: bool = False) -> None:
    repo = SupabaseRepository()
    exercise = repo.read_as_exercise(exercise_name)
    exercise_statement = exercise.statement

    prompt = (
        None
        if include_proof
        else PROMPT_FOR_EXERCISES.format(exercise=exercise_statement)
    )

    exercise_statement = exercise.statement

    run_agent(prompt, model)


if __name__ == "__main__":
    app()
