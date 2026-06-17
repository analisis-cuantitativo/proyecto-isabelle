from typing import Literal

from pydantic import BaseModel, Field

from proyecto_isabelle.sync.models import Source


class ExerciseResponse(BaseModel):
    id: int
    name: str
    source: Source
    topics: list[str] = Field(default_factory=list)
    requirements: list[str] | None = None
    is_verified: bool = False
    msc_code: str | None = None
    license: str | None = None
    proposed_thy_code: str | None = None
    corrected_thy_code: str | None = None
    statement: str | None = None
    proof: str | None = None


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
