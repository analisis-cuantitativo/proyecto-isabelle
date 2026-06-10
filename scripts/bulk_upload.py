from pathlib import Path

from proyecto_isabelle.util.constants import ROOT_DIR
from proyecto_isabelle.sync.operations import (
    load_exercise_from_path,
    upload_exercise_to_db,
)


def collect_exercises(path: Path, dry_run: bool = False):
    """Find all exercises on the path and use the  functions for load and upload all exercise at the database"""

    fails = []

    for topic in path.iterdir():
        if not topic.is_dir():
            continue

        for exercise in topic.iterdir():
            if not exercise.is_dir():
                continue

            if dry_run:
                print(f"Subiría la carpeta {exercise}")
                continue

            try:
                exercise_object = load_exercise_from_path(exercise)
                upload_exercise_to_db(exercise_object)
            except Exception as e:
                print(f"No pude subir {exercise} por {e}")
                fails.append(exercise)

    print(f"Fallaron: {fails}")


old_exercises = ROOT_DIR / "old_data" / "exercises_with_proof"
collect_exercises(old_exercises)
