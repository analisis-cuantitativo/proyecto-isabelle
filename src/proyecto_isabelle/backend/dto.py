from typing import Literal

from pydantic import BaseModel, Field

from proyecto_isabelle.sync.models import Exercise


class ExerciseResponse(Exercise):
    id: int


type ReviewDecision = Literal["approved", "rejected"]


class ReviewRequest(BaseModel):
    decision: ReviewDecision
    corrected_thy_code: str


class IsabelleValidationResult(BaseModel):
    is_valid: bool
    errors: list[str] = Field(default_factory=list)
    warnings: list[str] = Field(default_factory=list)


class ReviewResponse(BaseModel):
    success: bool
    isabelle_validation: IsabelleValidationResult | None = None


class CategoryResponse(BaseModel):
    name: str
    exercise_count: int
