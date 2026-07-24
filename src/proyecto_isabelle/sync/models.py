from typing import Any

from datetime import datetime, timezone

from pydantic import BaseModel, Field


class Source(BaseModel):
    title: str
    authors: list[str]
    section: str
    publication_year: int
    source_page: str


class Exercise(BaseModel):
    """Dedicated object for exercises using Pydantic, as requested in the issue"""

    name: str
    source: Source
    topics: list[str] | None = None
    requirements: list[str] | None = None
    is_verified: bool
    msc_code: str | None = None
    license: str | None = None
    proposed_thy_code: str | None = None
    corrected_thy_code: str | None = None
    statement: str | None = None
    proof: str | None = None


class Benchmark(BaseModel):
    """Contains the information about one agent being tested on one exercise."""

    exercise_id: int
    """The ID of the exercise."""

    model_name: str
    """The model's name."""

    was_given_the_correct_thy_statement: bool
    """Whether the model was given the human-verified .thy statement"""

    thy_results: list[str]
    """
    The proposals by the model, which is a list whose elements
    are the different passes in order.
    """

    thoughts: list[str | None]
    """The chain of thoughts, if any, for each pass."""

    tokens_consumed: int
    """The number of tokens consumed by the model."""

    num_of_passes: int
    """How many attempts were given to the model.

    For this benchmark, we give the model the errors
    that Isabelle raises up to `n` times, where `n`
    is defined by the field `max_num_of_passes`.
    """

    max_num_of_passes: int = 3
    """The maximum number of attempts the model gets."""

    correctly_verified: bool
    """Whether the model correctly verified the proof."""

    deepisahol_metadata: list[dict[str, Any]]
    """The DeepIsaHOL metadata for each pass."""

    created_at: datetime = Field(default_factory=lambda: datetime.now(tz=timezone.utc))
    """When the row was created."""
