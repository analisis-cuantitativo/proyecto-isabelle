"""Exercise-proving agent built on ``pydantic_ai``.

Replaces the hand-rolled generate -> regex-extract -> verify -> retry loop in
``query/agent.py`` with a single agent run: the model is given a
``check_in_isabelle`` tool and calls it itself, as many times as it needs,
before returning a structured ``ProofAttempt``. ``output_validator`` rejects
(and triggers an automatic retry on) any answer that still contains
``sorry``/``oops``.

This only covers the synchronous, single-exercise path. Batch processing
(``query/llm/batch.py``) uses Anthropic's Message Batches API directly, which
``pydantic_ai`` doesn't wrap, so it stays as-is.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field

from pydantic import BaseModel, Field
from pydantic_ai import Agent, ModelRetry, RunContext, UsageLimits
from pydantic_ai.exceptions import UnexpectedModelBehavior, UsageLimitExceeded
from pydantic_ai.models.anthropic import AnthropicModel, AnthropicModelSettings
from pydantic_ai.providers.anthropic import AnthropicProvider

from proyecto_isabelle.prompts.render import PreviousAttempt, render_exercise_prompt
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm.config import get_config

logger = logging.getLogger(__name__)

DEFAULT_MODEL = "anthropic/claude-sonnet-4-5-20250929"


class ProofAttempt(BaseModel):
    """A candidate, model-produced .thy file for one exercise."""

    theory_name: str = Field(description="The name after `theory` in the .thy header")
    thy_content: str = Field(description="Full contents of the .thy file")


class IsabelleCheck(BaseModel):
    """A single ``check_in_isabelle`` call the agent made during one run."""

    thy_content: str
    verified: bool
    errors: list[str]


@dataclass
class ProofResult:
    """Everything a caller needs: the final attempt, plus the retry trail."""

    attempt: ProofAttempt
    checks: list[IsabelleCheck]
    request_count: int
    total_tokens: int
    max_isabelle_checks: int


class ProofBudgetExceeded(Exception):
    """Raised when the agent run ended without settling on a final answer —
    either it used its full request budget, or it exhausted its output
    retries (e.g. repeatedly ignoring an output validator). Carries whatever
    ``check_in_isabelle`` calls happened before that, so callers can still
    inspect the last attempts made."""

    def __init__(self, checks: list[IsabelleCheck]):
        self.checks = checks
        super().__init__(
            f"Run ended after {len(checks)} Isabelle check(s) without "
            "producing a final answer."
        )


@dataclass
class ProofDeps:
    exercise: str
    proof: str | None = None
    proposed_thy_code: str | None = None
    previous_attempts: list[PreviousAttempt] = field(default_factory=list)
    max_isabelle_checks: int = 5
    checks: list[IsabelleCheck] = field(default_factory=list)


def build_proof_agent(
    model_name: str = DEFAULT_MODEL,
    thinking_budget: int | None = 4096,
    output_retries: int = 3,
) -> Agent[ProofDeps, ProofAttempt]:
    """Construct a fresh proof agent for the given model.

    ``model_name`` follows this repo's ``"anthropic/<model>"`` convention
    (see ``util.constants.MODELS``), not pydantic_ai's ``"anthropic:<model>"``.

    ``output_retries`` bounds how many times the ``sorry``/``oops``
    output-validator check below can send the model back for another attempt.
    It does NOT bound how many times the model calls ``check_in_isabelle``
    (that tool never raises ``ModelRetry``) — see ``ProofDeps.max_isabelle_checks``
    and ``prove_exercise``'s ``max_requests`` for that.

    A fresh instance per call keeps these settings configurable per run
    without module-level mutable state.
    """
    config = get_config()
    model = AnthropicModel(
        model_name.removeprefix("anthropic/"),
        provider=AnthropicProvider(api_key=config.anthropic_api_key),
    )

    settings: AnthropicModelSettings = {}
    if thinking_budget is not None:
        # Extended thinking requires temperature 1 (matches query/agent.py).
        settings["anthropic_thinking"] = {
            "type": "enabled",
            "budget_tokens": thinking_budget,
        }
        settings["max_tokens"] = thinking_budget * 4
        settings["temperature"] = 1.0

    agent: Agent[ProofDeps, ProofAttempt] = Agent(
        model,
        deps_type=ProofDeps,
        output_type=ProofAttempt,
        model_settings=settings or None,
        output_retries=output_retries,
    )

    @agent.system_prompt
    def _build_system_prompt(ctx: RunContext[ProofDeps]) -> str:
        return render_exercise_prompt(
            exercise=ctx.deps.exercise,
            proof=ctx.deps.proof,
            proposed_thy_code=ctx.deps.proposed_thy_code,
            previous_attempts=ctx.deps.previous_attempts,
        )

    @agent.tool
    def check_in_isabelle(ctx: RunContext[ProofDeps], thy_content: str) -> str:
        """Type-check and run ``thy_content`` against Isabelle; reports errors, if any.

        Call this before returning a final answer. If it reports failures,
        fix them and call it again with the corrected content. There is a
        limited number of calls available for this exercise.
        """
        if len(ctx.deps.checks) >= ctx.deps.max_isabelle_checks:
            return (
                f"Check budget exhausted ({ctx.deps.max_isabelle_checks} calls "
                "used). Stop iterating and return your best attempt as the "
                "final answer now, even if it still fails."
            )

        result = query_content(thy_content, mode="build")
        ctx.deps.checks.append(
            IsabelleCheck(
                thy_content=thy_content,
                verified=result.verified,
                errors=result.errors,
            )
        )
        if result.verified:
            return "OK: the proof builds and contains no sorry/oops."
        return f"FAILED: {'; '.join(result.errors) or result.message}"

    @agent.output_validator
    def _no_sorry_or_oops(
        ctx: RunContext[ProofDeps], output: ProofAttempt
    ) -> ProofAttempt:
        lowered = output.thy_content
        if "sorry" in lowered or "oops" in lowered:
            raise ModelRetry(
                "The returned thy_content still contains `sorry` or `oops` — "
                "call check_in_isabelle again and return a complete proof."
            )
        return output

    @agent.output_validator
    def _must_have_checked(
        ctx: RunContext[ProofDeps], output: ProofAttempt
    ) -> ProofAttempt:
        """Reject a final answer the model never ran through Isabelle.

        Without this, the model can (and often does) skip the tool entirely
        and submit a first-draft guess — the only feedback it ever gets is
        then the caller's independent re-verification, after the run is
        already over. This forces at least one real check_in_isabelle round
        trip per run, so the model always sees genuine Isabelle errors (and
        a chance to fix them) before finalizing.
        """
        if not ctx.deps.checks:
            raise ModelRetry(
                "You haven't called check_in_isabelle yet. Call it on this "
                "thy_content before submitting a final answer."
            )
        return output

    return agent


async def prove_exercise(
    exercise: str,
    proof: str | None = None,
    proposed_thy_code: str | None = None,
    previous_attempts: list[PreviousAttempt] | None = None,
    model_name: str = DEFAULT_MODEL,
    thinking_budget: int | None = 4096,
    max_isabelle_checks: int = 5,
    output_retries: int = 3,
    max_requests: int | None = None,
) -> ProofResult:
    """Run the agent end-to-end and return its final, verified-or-not attempt
    together with the trail of Isabelle checks it made along the way.

    Two independent knobs bound the retry loop:
    - ``max_isabelle_checks``: a soft cap. Once hit, ``check_in_isabelle``
      stops calling Isabelle and just tells the model to submit its best
      attempt — cheap, and gives the model a chance to wrap up gracefully.
    - ``max_requests`` (default ``2 * max_isabelle_checks + output_retries + 2``):
      a hard cap on total LLM requests in the run (``UsageLimits.request_limit``),
      in case the model ignores the soft cap. Raises ``ProofBudgetExceeded``
      (with whatever checks happened) if hit before a final answer.

    A third, output-level guard (an ``output_validator``) rejects any final
    answer the model hasn't run through ``check_in_isabelle`` at least once,
    forcing a real verification round trip every run. If the model keeps
    ignoring that (or the sorry/oops check) past ``output_retries``,
    pydantic_ai raises ``UnexpectedModelBehavior``, which is also folded into
    ``ProofBudgetExceeded`` here.

    Every ``check_in_isabelle`` call is recorded in the returned
    ``ProofResult.checks``, regardless of which cap ends the run.
    """
    agent = build_proof_agent(
        model_name=model_name,
        thinking_budget=thinking_budget,
        output_retries=output_retries,
    )
    deps = ProofDeps(
        exercise=exercise,
        proof=proof,
        proposed_thy_code=proposed_thy_code,
        previous_attempts=previous_attempts or [],
        max_isabelle_checks=max_isabelle_checks,
    )
    usage_limits = UsageLimits(
        request_limit=max_requests or (2 * max_isabelle_checks + output_retries + 2)
    )

    try:
        result = await agent.run(
            "Formalize and prove the exercise.", deps=deps, usage_limits=usage_limits
        )
    except (UsageLimitExceeded, UnexpectedModelBehavior) as e:
        logger.warning(
            "Proof agent aborted after %d Isabelle check(s): %s",
            len(deps.checks),
            e,
        )
        raise ProofBudgetExceeded(deps.checks) from e

    usage = result.usage()
    logger.info(
        "Proof agent finished after %d Isabelle check(s) (requests=%s)",
        len(deps.checks),
        usage.requests,
    )
    return ProofResult(
        attempt=result.output,
        checks=deps.checks,
        request_count=usage.requests,
        total_tokens=usage.input_tokens + usage.output_tokens,
        max_isabelle_checks=max_isabelle_checks,
    )
