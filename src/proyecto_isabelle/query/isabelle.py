from typing import Optional
from pathlib import Path

import httpx
from pydantic import BaseModel, Field

from proyecto_isabelle.parse import thy

DEFAULT_TIMEOUT = 60


class IsabelleRequest(BaseModel):
    """Request model for proof verification."""

    thy_content: str = Field(
        ..., description="The complete content of the .thy file to verify"
    )
    logic: str = Field(
        default="HOL", description="The Isabelle logic to use (e.g., HOL, HOL-Analysis)"
    )
    timeout_seconds: int = Field(
        default=300,
        ge=1,
        le=3600,
        description="Timeout in seconds for the verification",
    )


class IsabelleResponse(BaseModel):
    """Response model for proof verification."""

    success: bool = Field(
        ..., description="Whether the API call completed successfully"
    )
    verified: bool = Field(
        ..., description="Whether the proof was successfully verified"
    )
    errors: list[str] = Field(
        default_factory=list,
        description="List of error messages if verification failed",
    )
    state: Optional[str] = Field(
        default=None, description="The final Isabelle state after verification"
    )
    message: str = Field(..., description="Human-readable message about the result")


def _verify_server_is_running(api_url: str = "http://localhost:8000") -> None:
    with httpx.Client(timeout=DEFAULT_TIMEOUT) as client:
        try:
            resp = client.get(f"{api_url.rstrip('/')}/health")
        except (ConnectionError, httpx.ConnectError) as e:
            raise RuntimeError(
                "Couldn't connect to the DeepIsaHOL server. Did you remember "
                "to run `docker compose up` or to start the DeepIsaHOL server?"
            ) from e

        if resp.status_code != 200:
            raise RuntimeError(
                "DeepIsaHOL server is not healthy. Did you remember to run "
                "`docker compose up` or to start the DeepIsaHOL server?"
            )


def query_file(
    path: Path | str,
    api_url: str = "http://localhost:8000",
) -> IsabelleResponse:
    content = thy.load_text(path)
    return query_content(content, api_url=api_url)


def query_content(
    content: str, api_url: str = "http://localhost:8000"
) -> IsabelleResponse:
    _verify_server_is_running(api_url)
    payload = IsabelleRequest(thy_content=content)

    with httpx.Client(timeout=payload.timeout_seconds + 30) as client:
        raw_response = client.post(
            f"{api_url.rstrip('/')}/verify",
            json=payload.model_dump(mode="json"),
        )
        raw_response.raise_for_status()

    return IsabelleResponse.model_validate(raw_response.json())
