from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from proyecto_isabelle.backend.routers import exercises

app = FastAPI(title="Isabelle Reviewer API", version="1.0.0")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["http://localhost:5173"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

app.include_router(exercises.router)


@app.get("/api/health")
async def health():
    return {"status": "ok"}
