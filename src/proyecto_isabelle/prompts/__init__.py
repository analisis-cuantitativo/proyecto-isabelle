from proyecto_isabelle.prompts.exercises import (
    PROMPT_FOR_EXERCISES,
    PROMPT_FOR_EXERCISES_WITH_PROOF,
    PROMPT_FOR_EXERCISES_WITH_PROOF_AND_ERRORS,
    extract_thy_content,
)
from proyecto_isabelle.prompts.render import (
    PreviousAttempt,
    render_exercise_prompt,
    render_thy_content_proposal_prompt,
)
from proyecto_isabelle.prompts.thy_content import PROMPT_FOR_THY_CONTENT_PROPOSAL

__all__ = [
    # String-constant prompts (used by scripts/benchmark.py, scripts/e2e.py,
    # scripts/populate_proposed_thy.py). Prefer the Jinja-templated
    # render_* functions below for new code.
    "PROMPT_FOR_EXERCISES",
    "PROMPT_FOR_EXERCISES_WITH_PROOF",
    "PROMPT_FOR_EXERCISES_WITH_PROOF_AND_ERRORS",
    "PROMPT_FOR_THY_CONTENT_PROPOSAL",
    "PreviousAttempt",
    "extract_thy_content",
    "render_exercise_prompt",
    "render_thy_content_proposal_prompt",
]
