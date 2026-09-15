"""Jinja2 rendering for the prompt templates in ``prompts/templates/``.

Replaces the old pattern of building prompt variants by string-concatenating
constants (``PROMPT_FOR_EXERCISES_WITH_PROOF = PROMPT_FOR_EXERCISES + "..."``):
the optional "with proof" / "with previous attempts" sections are just
``{% if %}`` blocks in one template.
"""

from functools import lru_cache
from pathlib import Path
from typing import NamedTuple

from jinja2 import Environment, FileSystemLoader, StrictUndefined

TEMPLATES_DIR = Path(__file__).parent / "templates"


class PreviousAttempt(NamedTuple):
    """One prior, failed attempt to feed back to the model as context."""

    thy_content: str
    error_tail: list[str]


@lru_cache
def _env() -> Environment:
    return Environment(
        loader=FileSystemLoader(TEMPLATES_DIR),
        trim_blocks=True,
        lstrip_blocks=True,
        undefined=StrictUndefined,
    )


def render_exercise_prompt(
    exercise: str,
    proof: str | None = None,
    proposed_thy_code: str | None = None,
    previous_attempts: list[PreviousAttempt] | None = None,
) -> str:
    """Render the exercise-proving prompt.

    ``proof`` (a natural-language proof sketch), ``proposed_thy_code`` (an
    already-generated statement skeleton for this exercise, `sorry`/`oops`
    placeholder proof — see ``Exercise.proposed_thy_code`` and
    ``scripts/populate_proposed_thy.py``), and ``previous_attempts`` (failed
    .thy content plus the Isabelle errors it produced) are all optional and
    independently toggle their sections of the template.
    """
    return (
        _env()
        .get_template("exercise.md.jinja")
        .render(
            exercise=exercise,
            proof=proof,
            proposed_thy_code=proposed_thy_code,
            previous_attempts=previous_attempts or [],
            include_proof_methods=True,
        )
    )


def render_thy_content_proposal_prompt(exercise: str) -> str:
    """Render the statement-skeleton ("sorry" placeholder) prompt."""
    return (
        _env()
        .get_template("thy_content_proposal.md.jinja")
        .render(
            exercise=exercise,
            include_proof_methods=False,
        )
    )
