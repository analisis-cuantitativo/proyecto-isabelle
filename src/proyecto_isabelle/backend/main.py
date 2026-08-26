import os

from fastapi import Depends, FastAPI
from fastapi.middleware.cors import CORSMiddleware

from proyecto_isabelle.backend.routers import auth, exercises
from proyecto_isabelle.backend.security import verify_credentials

app = FastAPI(title="Isabelle Reviewer API", version="1.0.0")

cors_origin = [
    o.strip()
    for o in os.getenv("CORS_ALLOW_ORIGINS", "http://localhost:5173").split(",")
    if o.strip()
]

app.add_middleware(
    CORSMiddleware,
    allow_origins=cors_origin,
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

app.include_router(auth.router)
app.include_router(exercises.router, dependencies=[Depends(verify_credentials)])


@app.get("/api/health")
async def health():
    return {"status": "ok"}
