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
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any, cast

from pydantic import BaseModel, Field
from pydantic_ai import Agent, ModelRetry, RunContext, UsageLimits
from pydantic_ai.exceptions import (
    ModelAPIError,
    UnexpectedModelBehavior,
    UsageLimitExceeded,
)
from pydantic_ai.models import Model, infer_model
from pydantic_ai.models.anthropic import AnthropicModelSettings
from pydantic_ai.providers import Provider, infer_provider_class
from pydantic_ai.settings import ModelSettings

from proyecto_isabelle.prompts.render import PreviousAttempt, render_exercise_prompt
from proyecto_isabelle.query.isabelle import query_content
from proyecto_isabelle.query.llm.config import LLMConfig, get_config
from proyecto_isabelle.query.run_log import RunLogWriter

logger = logging.getLogger(__name__)

DEFAULT_MODEL = "anthropic:claude-sonnet-4-5-20250929"

# Which `LLMConfig` field holds the API key for each pydantic_ai provider
# name (the part of a `Models` value before the `:`). Adding support for a
# new provider is just one line here — `_build_model` below delegates
# everything else (which Model/Provider class to use, how to talk to it) to
# pydantic_ai's own `infer_model`/`infer_provider_class` registry.
_PROVIDER_API_KEY_FIELDS: dict[str, str] = {
    "anthropic": "anthropic_api_key",
    "openai": "openai_api_key",
    # Same OpenAI account/key as "openai" — just routes through the Responses
    # API (pydantic_ai's OpenAIResponsesModel) instead of Chat Completions.
    # Needed for model families (e.g. GPT-5.6 Terra/Luna) that 400 on
    # function-tool requests over Chat Completions unless reasoning is
    # disabled entirely; the Responses API supports tools + reasoning together.
    "openai-responses": "openai_api_key",
    "google-gla": "google_api_key",
    "deepseek": "deepseek_api_key",
    "moonshotai": "moonshotai_api_key",
}


def _build_model(model_name: str, config: LLMConfig) -> Model:
    """Build a pydantic_ai ``Model`` from a ``"<provider>:<model>"`` string.

    Delegates to pydantic_ai's ``infer_model``, which already knows how to
    turn e.g. ``"deepseek:deepseek-chat"`` or ``"google-gla:gemini-3-1-pro"``
    into the right ``Model``/``Provider`` pair — we only need to supply the
    right API key, sourced from ``LLMConfig`` rather than the environment
    (which is what pydantic_ai's default provider factory reads).
    """
    provider_name, sep, _ = model_name.partition(":")
    if not sep or provider_name not in _PROVIDER_API_KEY_FIELDS:
        known = ", ".join(sorted(_PROVIDER_API_KEY_FIELDS))
        raise ValueError(
            f"Don't know how to authenticate provider {provider_name!r} "
            f"(from model {model_name!r}). Known providers: {known}. Add a "
            "new entry to _PROVIDER_API_KEY_FIELDS (and an API key field on "
            "LLMConfig) to support it."
        )

    api_key = getattr(config, _PROVIDER_API_KEY_FIELDS[provider_name])

    def _provider_factory(name: str) -> Provider[Any]:
        # Every provider class pydantic_ai ships accepts `api_key` as a
        # keyword-only argument, but that's not expressible on the shared
        # `Provider` base type, so this dynamic dispatch can't be statically
        # checked.
        provider_class = infer_provider_class(name)
        return provider_class(api_key=api_key)  # pyright: ignore[reportCallIssue]

    return infer_model(model_name, provider_factory=_provider_factory)


class ProofAttempt(BaseModel):
    """A candidate, model-produced .thy file for one exercise."""

    theory_name: str = Field(description="The name after `theory` in the .thy header")
    thy_content: str = Field(description="Full contents of the .thy file")


class IsabelleCheck(BaseModel):
    """A single ``check_in_isabelle`` call the agent made during one run."""

    thy_content: str
    verified: bool
    errors: list[str]
    tokens_consumed: int = 0
    """Cumulative input+output tokens through this pass (i.e. including every
    prior pass in the same run), sourced from the live ``RunUsage`` pydantic_ai
    updates after each model response — not a per-pass delta."""


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
    build_timeout_seconds: int = 300
    checks: list[IsabelleCheck] = field(default_factory=list)
    on_check: Callable[[IsabelleCheck], None] | None = None
    """Fired synchronously right after each real ``check_in_isabelle`` call is
    recorded, so a caller can persist it immediately rather than waiting for
    the run to finish — see ``prove_exercise``'s ``on_check`` param."""


def build_proof_agent(
    model_name: str = DEFAULT_MODEL,
    thinking_budget: int | None = 4096,
    output_retries: int = 3,
) -> Agent[ProofDeps, ProofAttempt]:
    """Construct a fresh proof agent for the given model.

    ``model_name`` follows pydantic_ai's own ``"<provider>:<model>"``
    convention (see ``util.constants.Models``) — e.g. ``"deepseek:deepseek-chat"``
    or ``"google-gla:gemini-3-1-pro"``, not just Anthropic models.

    ``output_retries`` bounds how many times the ``sorry``/``oops``
    output-validator check below can send the model back for another attempt.
    It does NOT bound how many times the model calls ``check_in_isabelle``
    (that tool never raises ``ModelRetry``) — see ``ProofDeps.max_isabelle_checks``
    and ``prove_exercise``'s ``max_requests`` for that.

    A fresh instance per call keeps these settings configurable per run
    without module-level mutable state.
    """
    model = _build_model(model_name, get_config())

    settings: ModelSettings = {}
    if thinking_budget is not None:
        settings["max_tokens"] = thinking_budget * 4
        settings["temperature"] = 1.0
        if model_name.startswith("anthropic:"):
            # Extended thinking requires temperature 1 (matches query/agent.py).
            # This setting is Anthropic-specific; other providers just get the
            # max_tokens/temperature above.
            cast(AnthropicModelSettings, settings)["anthropic_thinking"] = {
                "type": "enabled",
                "budget_tokens": thinking_budget,
            }

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

        result = query_content(
            thy_content,
            mode="build",
            timeout_seconds=ctx.deps.build_timeout_seconds,
        )
        check = IsabelleCheck(
            thy_content=thy_content,
            verified=result.verified,
            errors=result.errors,
            tokens_consumed=ctx.usage.input_tokens + ctx.usage.output_tokens,
        )
        ctx.deps.checks.append(check)
        if ctx.deps.on_check:
            ctx.deps.on_check(check)
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
    run_logger: RunLogWriter | None = None,
    build_timeout_seconds: int = 300,
    on_check: Callable[[IsabelleCheck], None] | None = None,
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
    - ``build_timeout_seconds``: per-``check_in_isabelle`` call, how long the
      DeepIsaHOL server is allowed to spend on ``isabelle build`` before it
      reports "Build timed out". Heavier exercises (e.g. those pulling in
      HOL-Analysis) can legitimately take longer than the 300s default.

    A third, output-level guard (an ``output_validator``) rejects any final
    answer the model hasn't run through ``check_in_isabelle`` at least once,
    forcing a real verification round trip every run. If the model keeps
    ignoring that (or the sorry/oops check) past ``output_retries``,
    pydantic_ai raises ``UnexpectedModelBehavior``, which is also folded into
    ``ProofBudgetExceeded`` here — as is ``ModelAPIError`` (e.g. a 4xx/5xx
    from the provider mid-run), so a request that a given provider rejects
    (deepseek-reasoner has been the one triggering this in practice) still
    persists whatever checks happened before it, instead of losing the run
    silently.

    Every ``check_in_isabelle`` call is recorded in the returned
    ``ProofResult.checks``, regardless of which cap ends the run.

    If ``run_logger`` is given (already started by the caller, via
    ``RunLogWriter.log_started``), every node of the run (model thinking,
    text, tool calls, tool returns) is appended to its JSONL log as it
    happens — see ``query/run_log.py``. This is why the agent is driven via
    ``agent.iter()`` below instead of the simpler ``agent.run()``: only
    ``iter()`` exposes each step as it's produced, rather than only the
    final result.

    If ``on_check`` is given, it's called synchronously right after each real
    ``check_in_isabelle`` call, so a caller can persist that pass immediately
    (e.g. to Supabase) instead of only getting the full trail once the run
    ends — see ``ProofDeps.on_check``.
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
        build_timeout_seconds=build_timeout_seconds,
        on_check=on_check,
    )
    usage_limits = UsageLimits(
        request_limit=max_requests or (2 * max_isabelle_checks + output_retries + 2)
    )

    try:
        async with agent.iter(
            "Formalize and prove the exercise.", deps=deps, usage_limits=usage_limits
        ) as agent_run:
            async for node in agent_run:
                if run_logger:
                    run_logger.log_node(node)
        assert agent_run.result is not None
        result = agent_run.result
    except (UsageLimitExceeded, UnexpectedModelBehavior, ModelAPIError) as e:
        logger.warning(
            "Proof agent aborted after %d Isabelle check(s): %s",
            len(deps.checks),
            e,
        )
        if run_logger:
            run_logger.log_event({"type": "aborted", "reason": str(e)})
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
