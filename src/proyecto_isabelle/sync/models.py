from datetime import datetime, timezone
from uuid import UUID

from pydantic import BaseModel, Field


class Source(BaseModel):
    title: str
    authors: list[str]
    section: str
    publication_year: int
    source_page: str


class Exercise(BaseModel):
    """Dedicated object for exercises using Pydantic, as requested in the issue"""

    id: int | None = None
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
    """One pass (one `check_in_isabelle` call) within a proof-agent run.

    A single run against one exercise produces one row per pass, all sharing
    the same ``run_id``; the row with the highest ``pass_number`` is the
    run's final, independently-reverified answer. This trades the old
    "one row per run, with list-of-passes columns" shape for one row per
    pass, so per-pass data (did *this* attempt verify, what errors did *it*
    get) is queryable/filterable directly instead of living in parallel
    arrays that have to be unpacked and zipped back together by index.
    """

    run_id: UUID
    """Shared by every pass of the same exercise+model attempt."""

    pass_number: int
    """1-indexed position of this pass within its run."""

    exercise_id: int
    """The ID of the exercise."""

    model_name: str
    """The model's name."""

    was_given_the_correct_thy_statement: bool
    """Whether the model was given the human-verified .thy statement.

    A run-level fact (the prompt is the same for every pass), duplicated
    across the run's rows.
    """

    thy_content: str
    """The model's proposed .thy content for this pass."""

    verified: bool
    """Whether this specific pass verified in Isabelle."""

    errors: list[str]
    """Isabelle's errors for this pass, if any."""

    max_num_of_passes: int
    """The maximum number of passes the model was allowed for this run."""

    hit_retry_budget: bool = False
    """Whether the run stopped because it exhausted its retry budget, rather
    than the model voluntarily submitting a final answer. Passes are written
    as they happen, before this is known, so it starts ``False`` on every row
    and gets patched to ``True`` for the whole run (by ``run_id``) once the
    run actually aborts — see ``SupabaseRepository.mark_run_hit_retry_budget``."""

    tokens_consumed: int
    """Cumulative input+output tokens through this pass (i.e. including every
    prior pass in the same run), not a per-pass delta. The highest
    ``pass_number`` row's value is the run's total."""

    created_at: datetime = Field(default_factory=lambda: datetime.now(tz=timezone.utc))
    """When the row was created."""
