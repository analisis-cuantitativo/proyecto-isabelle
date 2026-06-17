from proyecto_isabelle.backend.dto import (
    ExerciseResponse,
    ReviewRequest,
    ReviewResponse,
)
from proyecto_isabelle.backend.repository import get_repository
from proyecto_isabelle.backend.services.isabelle_validator import (
    validate_isabelle_code,
)


def get_pending_exercises() -> list[ExerciseResponse]:
    exercises, _next = get_repository().list_exercises(
        limit=500, after_id=None, is_verified=False
    )
    return exercises


def list_exercises(
    *,
    limit: int = 50,
    after_id: int | None = None,
    is_verified: bool | None = None,
) -> tuple[list[ExerciseResponse], int | None]:
    return get_repository().list_exercises(
        limit=limit, after_id=after_id, is_verified=is_verified
    )


def get_exercise_by_id(exercise_id: int) -> ExerciseResponse | None:
    return get_repository().get_exercise_by_id(exercise_id)


def get_exercise_by_name(name: str) -> ExerciseResponse | None:
    return get_repository().get_exercise_by_name(name)


def submit_review(exercise_id: int, request: ReviewRequest) -> ReviewResponse:
    validation = validate_isabelle_code(request.corrected_thy_code)

    update_payload: dict = {
        "corrected_thy_code": request.corrected_thy_code,
    }
    if request.decision == "approved":
        update_payload["is_verified"] = True
    else:
        update_payload["is_verified"] = False

    get_repository().update_exercise(exercise_id, update_payload)

    return ReviewResponse(success=True, isabelle_validation=validation)


def get_categories() -> list:
    raise NotImplementedError("categories not yet implemented")
