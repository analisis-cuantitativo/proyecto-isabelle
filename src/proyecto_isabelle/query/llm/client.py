"""LLM client implementation using LiteLLM."""

import os

import litellm

from .config import LLMConfig, get_config
from .models import LLMResponse, Message, TokenUsage


class LLMClient:
    """Client for interacting with various LLM providers via LiteLLM."""

    def __init__(self, config: LLMConfig | None = None):
        """Initialize the LLM client.

        Args:
            config: Optional configuration. If not provided, uses global config.
        """
        self.config = config or get_config()
        self._setup_environment()

    def _setup_environment(self) -> None:
        """Set up environment variables for LiteLLM."""
        if self.config.openai_api_key:
            os.environ["OPENAI_API_KEY"] = self.config.openai_api_key
        if self.config.anthropic_api_key:
            os.environ["ANTHROPIC_API_KEY"] = self.config.anthropic_api_key
        if self.config.google_api_key:
            os.environ["GOOGLE_API_KEY"] = self.config.google_api_key

    def _get_base_url(self, model: str) -> str | None:
        """Get the base URL for a model if needed."""
        if model.startswith("ollama/"):
            return self.config.ollama_base_url
        if model.startswith("lm-studio/"):
            return self.config.lm_studio_base_url
        return None

    def _normalize_model(self, model: str) -> str:
        """Normalize model name for LiteLLM."""
        # LM Studio uses OpenAI-compatible API
        if model.startswith("lm-studio/"):
            return "openai/" + model.removeprefix("lm-studio/")
        return model

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
            model: Model identifier. If not provided, uses default from config.
            temperature: Sampling temperature (0.0 to 2.0).
            max_tokens: Maximum tokens in the response.
            stop: Stop sequences.
            thinking_budget: Token budget for extended thinking (Claude only).
                If provided, enables extended thinking with the specified budget.
                max_tokens must be greater than thinking_budget.

        Returns:
            LLMResponse with the completion result.
        """
        model = model or self.config.llm_default_model
        normalized_model = self._normalize_model(model)
        base_url = self._get_base_url(model)

        # Convert messages to dict format for LiteLLM
        message_dicts = [{"role": m.role, "content": m.content} for m in messages]

        try:
            # Build kwargs for litellm
            kwargs: dict = {
                "model": normalized_model,
                "messages": message_dicts,
                "temperature": temperature,
                "timeout": self.config.llm_default_timeout,
            }

            if max_tokens is not None:
                kwargs["max_tokens"] = max_tokens
            if stop is not None:
                kwargs["stop"] = stop
            if base_url is not None:
                kwargs["api_base"] = base_url
            if thinking_budget is not None:
                kwargs["thinking"] = {
                    "type": "enabled",
                    "budget_tokens": thinking_budget,
                }

            response = litellm.completion(**kwargs)

            # Extract usage info
            usage = None
            if hasattr(response, "usage") and response.usage:  # pyright: ignore
                usage = TokenUsage(
                    prompt_tokens=response.usage.prompt_tokens or 0,  # pyright: ignore
                    completion_tokens=response.usage.completion_tokens  # pyright: ignore
                    or 0,
                    total_tokens=response.usage.total_tokens or 0,  # pyright: ignore
                )

            # Extract content and thinking
            content = None
            thinking = None
            if response.choices and len(response.choices) > 0:  # pyright: ignore
                message = response.choices[0].message  # pyright: ignore
                content = message.content
                if hasattr(message, "thinking") and message.thinking:  # pyright: ignore
                    thinking = message.thinking  # pyright: ignore

            return LLMResponse(
                success=True,
                content=content,
                thinking=thinking,
                model=response.model,
                usage=usage,
            )

        except litellm.exceptions.AuthenticationError as e:
            return LLMResponse(
                success=False,
                error=f"Authentication failed: {e}",
                model=model,
            )
        except litellm.exceptions.BadRequestError as e:
            return LLMResponse(
                success=False,
                error=f"Bad request: {e}",
                model=model,
            )
        except litellm.exceptions.RateLimitError as e:
            return LLMResponse(
                success=False,
                error=f"Rate limit exceeded: {e}",
                model=model,
            )
        except litellm.exceptions.APIConnectionError as e:
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
            model: Model identifier. If not provided, uses default from config.
            temperature: Sampling temperature (0.0 to 2.0).
            max_tokens: Maximum tokens in the response.
            thinking_budget: Token budget for extended thinking (Claude only).

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
        model: Model identifier. If not provided, uses default from config.
        temperature: Sampling temperature (0.0 to 2.0).
        max_tokens: Maximum tokens in the response.
        stop: Stop sequences.
        thinking_budget: Token budget for extended thinking (Claude only).

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
        model: Model identifier. If not provided, uses default from config.
        temperature: Sampling temperature (0.0 to 2.0).
        max_tokens: Maximum tokens in the response.
        thinking_budget: Token budget for extended thinking (Claude only).

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
