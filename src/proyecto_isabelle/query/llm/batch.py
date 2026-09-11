"""Batch completion support using Anthropic's Message Batches API.

Synchronous ``ask()``/``complete()`` calls hold one HTTP connection open for
the whole generation (worse with a large ``max_tokens``/``thinking_budget``),
which is what times out under flaky networks or long queue times. Message
Batches replace that with two kinds of request that never block for long:
submitting the batch (returns immediately) and polling its status (a cheap
GET), with the actual generation happening server-side. This is Anthropic-
only, since it's the only configured provider that offers a batch endpoint.

Example usage:
    from proyecto_isabelle.query.llm import batch

    batch_id = batch.create_batch(
        {"ex-1": "Prove 1+1=2", "ex-2": "Prove 2+2=4"},
        model="claude-opus-4-6",
        max_tokens=8192,
    )
    batch.wait_for_batch(batch_id)
    results = batch.get_batch_results(batch_id)  # {"ex-1": LLMResponse(...), ...}
"""

from __future__ import annotations

import time
from collections.abc import Callable

from anthropic.types.messages.message_batch import MessageBatch

from .client import _response_from_anthropic_message, get_client
from .models import LLMResponse

DEFAULT_POLL_INTERVAL_SECONDS = 30.0


def create_batch(
    prompts: dict[str, str],
    model: str,
    system: str | None = None,
    temperature: float = 1.0,
    max_tokens: int = 4096,
    thinking_budget: int | None = None,
) -> str:
    """Submit a Message Batch and return its batch id.

    Args:
        prompts: Maps a caller-chosen ``custom_id`` (unique within the batch,
            e.g. the exercise name) to the user prompt for that request.
        model: Anthropic model name, without the ``anthropic/`` prefix.
        system: Optional system message shared by every request in the batch.
        temperature: Sampling temperature. Ignored when ``thinking_budget``
            is set, since extended thinking requires temperature 1.
        max_tokens: Maximum tokens per response.
        thinking_budget: Token budget for extended thinking, if any.

    Returns:
        The batch id, to be passed to ``wait_for_batch``/``get_batch_results``.
    """
    client = get_client().get_anthropic_client()

    requests = []
    for custom_id, prompt in prompts.items():
        params: dict = {
            "model": model,
            "max_tokens": max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        }
        if system:
            params["system"] = system
        if thinking_budget is not None:
            params["thinking"] = {"type": "enabled", "budget_tokens": thinking_budget}
        else:
            params["temperature"] = temperature

        requests.append({"custom_id": custom_id, "params": params})

    batch = client.messages.batches.create(requests=requests)
    return batch.id


def wait_for_batch(
    batch_id: str,
    poll_interval: float = DEFAULT_POLL_INTERVAL_SECONDS,
    on_poll: Callable[[MessageBatch], None] | None = None,
) -> MessageBatch:
    """Block until the batch has finished processing.

    Args:
        batch_id: Id returned by ``create_batch``.
        poll_interval: Seconds to sleep between status checks.
        on_poll: Optional callback invoked with the ``MessageBatch`` after
            every status check (e.g. to render progress).

    Returns:
        The final ``MessageBatch``, once ``processing_status == "ended"``.
    """
    client = get_client().get_anthropic_client()

    while True:
        current = client.messages.batches.retrieve(batch_id)
        if on_poll is not None:
            on_poll(current)
        if current.processing_status == "ended":
            return current
        time.sleep(poll_interval)


def get_batch_results(batch_id: str) -> dict[str, LLMResponse]:
    """Fetch the results of an ended batch, keyed by ``custom_id``."""
    client = get_client().get_anthropic_client()

    results: dict[str, LLMResponse] = {}
    for entry in client.messages.batches.results(batch_id):
        result = entry.result
        if result.type == "succeeded":
            results[entry.custom_id] = _response_from_anthropic_message(result.message)
        elif result.type == "errored":
            results[entry.custom_id] = LLMResponse(
                success=False, error=str(result.error)
            )
        elif result.type == "canceled":
            results[entry.custom_id] = LLMResponse(
                success=False, error="Request was canceled"
            )
        elif result.type == "expired":
            results[entry.custom_id] = LLMResponse(
                success=False, error="Request expired before it was processed"
            )

    return results


def run_batch(
    prompts: dict[str, str],
    model: str,
    system: str | None = None,
    temperature: float = 1.0,
    max_tokens: int = 4096,
    thinking_budget: int | None = None,
    poll_interval: float = DEFAULT_POLL_INTERVAL_SECONDS,
    on_poll: Callable[[MessageBatch], None] | None = None,
) -> dict[str, LLMResponse]:
    """Convenience wrapper: submit a batch, wait for it, and fetch results."""
    batch_id = create_batch(
        prompts,
        model=model,
        system=system,
        temperature=temperature,
        max_tokens=max_tokens,
        thinking_budget=thinking_budget,
    )
    wait_for_batch(batch_id, poll_interval=poll_interval, on_poll=on_poll)
    return get_batch_results(batch_id)
