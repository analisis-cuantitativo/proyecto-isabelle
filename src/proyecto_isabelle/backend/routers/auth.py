from fastapi import APIRouter, Depends

from proyecto_isabelle.backend.security import verify_credentials

router = APIRouter(prefix="/api/auth", tags=["auth"])


@router.get("/login")
def login(username: str = Depends(verify_credentials)):
    return {"authenticated": True, "username": username}
