"""Pydantic models for the LLM module."""

from typing import Literal

from pydantic import BaseModel, Field


class Message(BaseModel):
    """A single message in a conversation."""

    role: Literal["system", "user", "assistant"]
    content: str


class TokenUsage(BaseModel):
    """Token usage statistics from an LLM response."""

    prompt_tokens: int = 0
    completion_tokens: int = 0
    total_tokens: int = 0


class LLMRequest(BaseModel):
    """Request parameters for an LLM completion."""

    messages: list[Message]
    model: str = Field(default="gpt-4o-mini")
    temperature: float = Field(default=0.7, ge=0.0, le=2.0)
    max_tokens: int | None = Field(default=None, gt=0)
    stop: list[str] | None = None


class LLMResponse(BaseModel):
    """Response from an LLM completion."""

    success: bool
    content: str | None = None
    thinking: str | None = None
    model: str | None = None
    usage: TokenUsage | None = None
    error: str | None = None
