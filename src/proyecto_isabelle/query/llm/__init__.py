"""LLM router submodule providing a unified interface for multiple LLM providers.

This module uses the anthropic and openai SDKs to support Anthropic, OpenAI,
Ollama, and LM Studio through a consistent Pydantic-based interface.

Example usage:
    from proyecto_isabelle.query import llm

    # Simple query with default model
    response = llm.ask("What is 2+2?")
    print(response.content)

    # With specific model and system prompt
    response = llm.ask(
        "Explain this theorem",
        model="anthropic/claude-sonnet-4-5-20250929",
        system="You are a math expert."
    )

    # Multi-turn conversation
    from proyecto_isabelle.query.llm import Message, complete

    messages = [
        Message(role="system", content="You are helpful."),
        Message(role="user", content="Hello!"),
    ]
    response = complete(messages, model="openai/gpt-4o")

Model name conventions (provider/model-name):
    - Anthropic: anthropic/claude-sonnet-4-5-20250929, anthropic/claude-opus-4-5-20251101
    - OpenAI: openai/gpt-4o, openai/gpt-4o-mini
    - Ollama: ollama/llama2, ollama/mistral
    - LM Studio: lm-studio/local-model
"""

from . import batch
from .client import LLMClient, ask, complete, get_client
from .config import LLMConfig, get_config
from .exceptions import LLMConfigError, LLMError, LLMProviderError
from .models import LLMRequest, LLMResponse, Message, TokenUsage

__all__ = [
    # Client
    "LLMClient",
    "ask",
    "complete",
    "get_client",
    # Batches (Anthropic only)
    "batch",
    # Config
    "LLMConfig",
    "get_config",
    # Models
    "Message",
    "LLMRequest",
    "LLMResponse",
    "TokenUsage",
    # Exceptions
    "LLMError",
    "LLMConfigError",
    "LLMProviderError",
]
