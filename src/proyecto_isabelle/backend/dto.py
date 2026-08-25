from typing import Literal

from pydantic import BaseModel

from proyecto_isabelle.sync.models import Exercise
from proyecto_isabelle.query.isabelle import IsabelleResponse


class ExerciseResponse(Exercise):
    id: int


type ReviewDecision = Literal["approved", "rejected"]


class ReviewRequest(BaseModel):
    decision: ReviewDecision
    corrected_thy_code: str


class VerifyRequest(BaseModel):
    corrected_thy_code: str


class ReviewResponse(BaseModel):
    success: bool
    isabelle_validation: IsabelleResponse | None = None


class CategoryResponse(BaseModel):
    name: str
    exercise_count: int
