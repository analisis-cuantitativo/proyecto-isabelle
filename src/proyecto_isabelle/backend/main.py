import os

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from proyecto_isabelle.backend.routers import exercises

app = FastAPI(title="Isabelle Reviewer API", version="1.0.0")

cors_origin = os.getenv("CORS_ALLOW_ORIGINS", "http://localhost:5173").split(",")

app.add_middleware(
    CORSMiddleware,
    allow_origins=cors_origin,
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

app.include_router(exercises.router)


@app.get("/api/health")
async def health():
    return {"status": "ok"}
