"""LLM client implementation using anthropic and openai SDKs."""

from typing import Literal

import anthropic
import openai

from .config import LLMConfig, get_config
from .models import LLMResponse, Message, TokenUsage

Provider = Literal["anthropic", "openai", "lm-studio", "ollama"]


def _response_from_anthropic_message(message: "anthropic.types.Message") -> LLMResponse:
    """Build an LLMResponse from an Anthropic ``Message``.

    Shared by the synchronous ``client.messages.create`` path and the
    Message Batches results path, since a batch's succeeded result wraps
    a ``Message`` of the same shape.
    """
    content_parts: list[str] = []
    thinking_parts: list[str] = []

    for block in message.content:
        if block.type == "text":
            content_parts.append(block.text)
        elif block.type == "thinking":
            thinking_parts.append(block.thinking)

    usage = TokenUsage(
        prompt_tokens=message.usage.input_tokens,
        completion_tokens=message.usage.output_tokens,
        total_tokens=message.usage.input_tokens + message.usage.output_tokens,
    )

    return LLMResponse(
        success=True,
        content="\n".join(content_parts) if content_parts else None,
        thinking="\n".join(thinking_parts) if thinking_parts else None,
        model=message.model,
        usage=usage,
    )


class LLMClient:
    """Client for interacting with various LLM providers."""

    def __init__(self, config: LLMConfig | None = None):
        """Initialize the LLM client.

        Args:
            config: Optional configuration. If not provided, uses global config.
        """
        self.config = config or get_config()
        self._anthropic_client: anthropic.Anthropic | None = None
        self._openai_client: openai.OpenAI | None = None
        self._lm_studio_client: openai.OpenAI | None = None
        self._ollama_client: openai.OpenAI | None = None

    def _get_anthropic_client(self) -> anthropic.Anthropic:
        """Get or create the Anthropic client."""
        if self._anthropic_client is None:
            self._anthropic_client = anthropic.Anthropic(
                api_key=self.config.anthropic_api_key,
                timeout=self.config.llm_default_timeout,
            )
        return self._anthropic_client

    def get_anthropic_client(self) -> anthropic.Anthropic:
        """Public accessor for the underlying Anthropic client.

        Used by the ``batch`` submodule, which needs the raw SDK client to
        drive the Message Batches endpoints directly.
        """
        return self._get_anthropic_client()

    def _get_openai_client(self) -> openai.OpenAI:
        """Get or create the OpenAI client."""
        if self._openai_client is None:
            self._openai_client = openai.OpenAI(
                api_key=self.config.openai_api_key,
                timeout=self.config.llm_default_timeout,
            )
        return self._openai_client

    def _get_lm_studio_client(self) -> openai.OpenAI:
        """Get or create the LM Studio client (OpenAI-compatible)."""
        if self._lm_studio_client is None:
            self._lm_studio_client = openai.OpenAI(
                base_url=self.config.lm_studio_base_url,
                api_key="lm-studio",  # LM Studio doesn't require a real API key
                timeout=self.config.llm_default_timeout,
            )
        return self._lm_studio_client

    def _get_ollama_client(self) -> openai.OpenAI:
        """Get or create the Ollama client (OpenAI-compatible)."""
        if self._ollama_client is None:
            self._ollama_client = openai.OpenAI(
                base_url=f"{self.config.ollama_base_url}/v1",
                api_key="ollama",  # Ollama doesn't require a real API key
                timeout=self.config.llm_default_timeout,
            )
        return self._ollama_client

    def _parse_model(self, model: str) -> tuple[Provider, str]:
        """Parse model string into provider and model name.

        Args:
            model: Model string like "anthropic/claude-sonnet-4-5-20250929"

        Returns:
            Tuple of (provider, model_name)
        """
        if model.startswith("anthropic/"):
            return "anthropic", model.removeprefix("anthropic/")
        elif model.startswith("openai/"):
            return "openai", model.removeprefix("openai/")
        elif model.startswith("lm-studio/"):
            return "lm-studio", model.removeprefix("lm-studio/")
        elif model.startswith("ollama/"):
            return "ollama", model.removeprefix("ollama/")
        else:
            # Default to OpenAI for backwards compatibility
            return "openai", model

    def _complete_anthropic(
        self,
        messages: list[Message],
        model: str,
        temperature: float,
        max_tokens: int | None,
        stop: list[str] | None,
        thinking_budget: int | None,
    ) -> LLMResponse:
        """Complete using Anthropic API."""
        client = self._get_anthropic_client()

        # Separate system message from other messages
        system_content: str | None = None
        conversation_messages: list[dict] = []

        for m in messages:
            if m.role == "system":
                system_content = m.content
            else:
                conversation_messages.append({"role": m.role, "content": m.content})

        try:
            kwargs: dict = {
                "model": model,
                "messages": conversation_messages,
                "max_tokens": max_tokens or 4096,
            }

            if system_content:
                kwargs["system"] = system_content
            if stop:
                kwargs["stop_sequences"] = stop

            # Handle extended thinking
            if thinking_budget is not None:
                kwargs["thinking"] = {
                    "type": "enabled",
                    "budget_tokens": thinking_budget,
                }
                # Temperature must be 1 for extended thinking
            else:
                kwargs["temperature"] = temperature

            response = client.messages.create(**kwargs)
            return _response_from_anthropic_message(response)

        except anthropic.AuthenticationError as e:
            return LLMResponse(
                success=False,
                error=f"Authentication failed: {e}",
                model=model,
            )
        except anthropic.BadRequestError as e:
            return LLMResponse(
                success=False,
                error=f"Bad request: {e}",
                model=model,
            )
        except anthropic.RateLimitError as e:
            return LLMResponse(
                success=False,
                error=f"Rate limit exceeded: {e}",
                model=model,
            )
        except anthropic.APIConnectionError as e:
            return LLMResponse(
                success=False,
                error=f"Connection error: {e}",
                model=model,
            )
        except Exception as e:
            return LLMResponse(
                success=False,
                error=f"Unexpected error: {e}",
                model=model,
            )

    def _complete_openai_compatible(
        self,
        client: openai.OpenAI,
        messages: list[Message],
        model: str,
        temperature: float,
        max_tokens: int | None,
        stop: list[str] | None,
    ) -> LLMResponse:
        """Complete using OpenAI-compatible API (OpenAI, LM Studio, Ollama)."""
        message_dicts = [{"role": m.role, "content": m.content} for m in messages]

        try:
            kwargs: dict = {
                "model": model,
                "messages": message_dicts,
                "temperature": temperature,
            }

            if max_tokens is not None:
                kwargs["max_tokens"] = max_tokens
            if stop is not None:
                kwargs["stop"] = stop

            response = client.chat.completions.create(**kwargs)

            # Extract usage info
            usage = None
            if response.usage:
                usage = TokenUsage(
                    prompt_tokens=response.usage.prompt_tokens or 0,
                    completion_tokens=response.usage.completion_tokens or 0,
                    total_tokens=response.usage.total_tokens or 0,
                )

            # Extract content
            content = None
            if response.choices and len(response.choices) > 0:
                content = response.choices[0].message.content

            return LLMResponse(
                success=True,
                content=content,
                model=response.model,
                usage=usage,
            )

        except openai.AuthenticationError as e:
            return LLMResponse(
                success=False,
                error=f"Authentication failed: {e}",
                model=model,
            )
        except openai.BadRequestError as e:
            return LLMResponse(
                success=False,
                error=f"Bad request: {e}",
                model=model,
            )
        except openai.RateLimitError as e:
            return LLMResponse(
                success=False,
                error=f"Rate limit exceeded: {e}",
                model=model,
            )
        except openai.APIConnectionError as e:
            return LLMResponse(
                success=False,
                error=f"Connection error: {e}",
                model=model,
            )
        except Exception as e:
            return LLMResponse(
                success=False,
                error=f"Unexpected error: {e}",
                model=model,
            )

    def complete(
        self,
        messages: list[Message],
        model: str | None = None,
        temperature: float = 0.7,
        max_tokens: int | None = None,
        stop: list[str] | None = None,
        thinking_budget: int | None = None,
    ) -> LLMResponse:
        """Send a completion request to the LLM.

        Args:
            messages: List of messages in the conversation.
            model: Model identifier with provider prefix (e.g., "anthropic/claude-sonnet-4-5-20250929").
                If not provided, uses default from config.
            temperature: Sampling temperature (0.0 to 2.0).
            max_tokens: Maximum tokens in the response.
            stop: Stop sequences.
            thinking_budget: Token budget for extended thinking (Anthropic only).
                If provided, enables extended thinking with the specified budget.

        Returns:
            LLMResponse with the completion result.
        """
        model = model or self.config.llm_default_model
        provider, model_name = self._parse_model(model)

        if provider == "anthropic":
            return self._complete_anthropic(
                messages=messages,
                model=model_name,
                temperature=temperature,
                max_tokens=max_tokens,
                stop=stop,
                thinking_budget=thinking_budget,
            )
        elif provider == "openai":
            return self._complete_openai_compatible(
                client=self._get_openai_client(),
                messages=messages,
                model=model_name,
                temperature=temperature,
                max_tokens=max_tokens,
                stop=stop,
            )
        elif provider == "lm-studio":
            return self._complete_openai_compatible(
                client=self._get_lm_studio_client(),
                messages=messages,
                model=model_name,
                temperature=temperature,
                max_tokens=max_tokens,
                stop=stop,
            )
        elif provider == "ollama":
            return self._complete_openai_compatible(
                client=self._get_ollama_client(),
                messages=messages,
                model=model_name,
                temperature=temperature,
                max_tokens=max_tokens,
                stop=stop,
            )
        else:
            return LLMResponse(
                success=False,
                error=f"Unknown provider: {provider}",
                model=model,
            )

    def ask(
        self,
        prompt: str,
        system: str | None = None,
        model: str | None = None,
        temperature: float = 0.7,
        max_tokens: int | None = None,
        thinking_budget: int | None = None,
    ) -> LLMResponse:
        """Convenience method for single-turn conversations.

        Args:
            prompt: The user's prompt.
            system: Optional system message.
            model: Model identifier with provider prefix. If not provided, uses default from config.
            temperature: Sampling temperature (0.0 to 2.0).
            max_tokens: Maximum tokens in the response.
            thinking_budget: Token budget for extended thinking (Anthropic only).

        Returns:
            LLMResponse with the completion result.
        """
        messages: list[Message] = []

        if system:
            messages.append(Message(role="system", content=system))

        messages.append(Message(role="user", content=prompt))

        return self.complete(
            messages=messages,
            model=model,
            temperature=temperature,
            max_tokens=max_tokens,
            thinking_budget=thinking_budget,
        )


# Module-level client instance (lazy loaded)
_client: LLMClient | None = None


def get_client() -> LLMClient:
    """Get the global LLM client instance."""
    global _client
    if _client is None:
        _client = LLMClient()
    return _client


def reset_client() -> None:
    """Reset the global client (useful for testing)."""
    global _client
    _client = None


def complete(
    messages: list[Message],
    model: str | None = None,
    temperature: float = 0.7,
    max_tokens: int | None = None,
    stop: list[str] | None = None,
    thinking_budget: int | None = None,
) -> LLMResponse:
    """Module-level complete function using the global client.

    Args:
        messages: List of messages in the conversation.
        model: Model identifier with provider prefix. If not provided, uses default from config.
        temperature: Sampling temperature (0.0 to 2.0).
        max_tokens: Maximum tokens in the response.
        stop: Stop sequences.
        thinking_budget: Token budget for extended thinking (Anthropic only).

    Returns:
        LLMResponse with the completion result.
    """
    return get_client().complete(
        messages=messages,
        model=model,
        temperature=temperature,
        max_tokens=max_tokens,
        stop=stop,
        thinking_budget=thinking_budget,
    )


def ask(
    prompt: str,
    system: str | None = None,
    model: str | None = None,
    temperature: float = 0.7,
    max_tokens: int | None = None,
    thinking_budget: int | None = None,
) -> LLMResponse:
    """Module-level ask function using the global client.

    Args:
        prompt: The user's prompt.
        system: Optional system message.
        model: Model identifier with provider prefix. If not provided, uses default from config.
        temperature: Sampling temperature (0.0 to 2.0).
        max_tokens: Maximum tokens in the response.
        thinking_budget: Token budget for extended thinking (Anthropic only).

    Returns:
        LLMResponse with the completion result.
    """
    return get_client().ask(
        prompt=prompt,
        system=system,
        model=model,
        temperature=temperature,
        max_tokens=max_tokens,
        thinking_budget=thinking_budget,
    )
