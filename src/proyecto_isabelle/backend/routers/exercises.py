from fastapi import APIRouter, HTTPException, Query

from proyecto_isabelle.backend.dto import (
    ExerciseResponse,
    ReviewRequest,
    ReviewResponse,
)
from proyecto_isabelle.backend.services.exercise_service import exercise_service

router = APIRouter(prefix="/api/exercises", tags=["exercises"])


@router.get("/pending")
def list_pending():
    exercises = exercise_service.get_pending_exercises()
    return {"exercises": exercises, "total": len(exercises)}


@router.get("")
def list_all(
    limit: int = Query(50, ge=1, le=200),
    after_id: int | None = Query(None, ge=0),
):
    exercises, next_after_id = exercise_service.list_exercises(
        limit=limit, after_id=after_id, is_verified=None
    )
    return {
        "exercises": exercises,
        "total": None,
        "next_after_id": next_after_id,
    }


@router.get("/{exercise_id}", response_model=ExerciseResponse)
def get_exercise(exercise_id: int):
    exercise = exercise_service.get_exercise_by_id(exercise_id)
    if not exercise:
        raise HTTPException(status_code=404, detail="Ejercicio no encontrado")
    return exercise


@router.get("/by-name/{exercise_name}", response_model=ExerciseResponse)
def get_exercise_by_name_route(exercise_name: str):
    exercise = exercise_service.get_exercise_by_name(exercise_name)
    if not exercise:
        raise HTTPException(status_code=404, detail="Ejercicio no encontrado")
    return exercise


@router.post("/{exercise_id}/review", response_model=ReviewResponse)
def review_exercise(exercise_id: int, request: ReviewRequest):
    exercise = exercise_service.get_exercise_by_id(exercise_id)
    if not exercise:
        raise HTTPException(status_code=404, detail="Ejercicio no encontrado")
    return exercise_service.submit_review(exercise_id, request)
