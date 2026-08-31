from proyecto_isabelle.backend.dto import (
    ExerciseResponse,
    ReviewRequest,
    ReviewResponse,
    VerifyRequest,
)
from proyecto_isabelle.backend.repository import get_repository
from proyecto_isabelle.backend.services.isabelle_validator import (
    validate_isabelle_code,
)
from proyecto_isabelle.query.isabelle import IsabelleResponse


class ExerciseService:
    def __init__(self) -> None:
        self.repo = get_repository()

    def get_pending_exercises(self) -> list[ExerciseResponse]:
        exercises, _next = self.repo.list_exercises(
            limit=1500, after_id=None, is_verified=False
        )
        return exercises

    def list_exercises(
        self,
        *,
        limit: int = 50,
        after_id: int | None = None,
        is_verified: bool | None = None,
    ) -> tuple[list[ExerciseResponse], int | None]:
        return self.repo.list_exercises(
            limit=limit, after_id=after_id, is_verified=is_verified
        )

    def get_exercise_by_id(self, exercise_id: int) -> ExerciseResponse | None:
        return self.repo.get_exercise_by_id(exercise_id)

    def get_exercise_by_name(self, name: str) -> ExerciseResponse | None:
        return self.repo.get_exercise_by_name(name)

    def verify_code(self, request: VerifyRequest) -> IsabelleResponse:
        return validate_isabelle_code(request.corrected_thy_code)

    def submit_review(self, exercise_id: int, request: ReviewRequest) -> ReviewResponse:
        validation = validate_isabelle_code(request.corrected_thy_code)

        if request.decision == "approved" and not validation.verified:
            return ReviewResponse(success=False, isabelle_validation=validation)

        update_payload: dict = {
            "corrected_thy_code": request.corrected_thy_code,
        }
        if request.decision == "approved":
            update_payload["is_verified"] = True
            self.repo.update_exercise(exercise_id, update_payload)
        else:
            update_payload["is_verified"] = False

        return ReviewResponse(success=True, isabelle_validation=validation)


exercise_service = ExerciseService()
