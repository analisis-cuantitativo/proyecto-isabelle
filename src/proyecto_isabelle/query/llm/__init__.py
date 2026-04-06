"""LLM router submodule providing a unified interface for multiple LLM providers.

This module uses LiteLLM internally to support OpenAI, Anthropic, Gemini,
Ollama, and LM Studio through a consistent Pydantic-based interface.

Example usage:
    from proyecto_isabelle.query import llm

    # Simple query with default model
    response = llm.ask("What is 2+2?")
    print(response.content)

    # With specific model and system prompt
    response = llm.ask(
        "Explain this theorem",
        model="claude-3-opus-20240229",
        system="You are a math expert."
    )

    # Multi-turn conversation
    from proyecto_isabelle.query.llm import Message, complete

    messages = [
        Message(role="system", content="You are helpful."),
        Message(role="user", content="Hello!"),
    ]
    response = complete(messages)

Model name conventions:
    - OpenAI: gpt-4, gpt-4o-mini
    - Anthropic: claude-3-opus-20240229, claude-3-sonnet-20240229
    - Gemini: gemini/gemini-pro
    - Ollama: ollama/llama2, ollama/mistral
    - LM Studio: lm-studio/local-model
"""

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
