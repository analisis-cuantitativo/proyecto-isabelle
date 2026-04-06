"""Custom exceptions for the LLM module."""


class LLMError(Exception):
    """Base exception for LLM-related errors."""

    pass


class LLMConfigError(LLMError):
    """Raised when there's a configuration error."""

    pass


class LLMProviderError(LLMError):
    """Raised when an LLM provider returns an error."""

    def __init__(self, message: str, provider: str | None = None):
        self.provider = provider
        super().__init__(message)
