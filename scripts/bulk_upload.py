from pathlib import Path

from proyecto_isabelle.util.constants import ROOT_DIR
from proyecto_isabelle.sync.operations import (
    load_exercise_from_path,
    upload_exercise_to_db,
)


def collect_exercises(path: Path):
    """Find all exercises on the path and use the  functions for load and upload all exercise at the database"""
    for topic in path.iterdir():
        if topic.is_dir():
            for exercise in topic.iterdir():
                if exercise.is_dir():
                    exercise_object = load_exercise_from_path(exercise)
                    upload_exercise_to_db(exercise_object)


old_exercises = ROOT_DIR / "old_data"
collect_exercises(old_exercises)
