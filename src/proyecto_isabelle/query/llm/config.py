"""Configuration for the LLM module using pydantic-settings."""

from pydantic_settings import BaseSettings, SettingsConfigDict


class LLMConfig(BaseSettings):
    """Configuration for LLM providers.

    All settings can be configured via environment variables.
    """

    model_config = SettingsConfigDict(
        env_file=".env",
        env_file_encoding="utf-8",
        extra="ignore",
    )

    # API keys for cloud providers
    openai_api_key: str | None = None
    anthropic_api_key: str | None = None
    google_api_key: str | None = None
    deepseek_api_key: str | None = None
    moonshotai_api_key: str | None = None

    # Local model endpoints
    ollama_base_url: str = "http://localhost:11434"
    lm_studio_base_url: str = "http://localhost:1234/v1"

    # Defaults
    llm_default_model: str = "openai/gpt-4o-mini"
    llm_default_timeout: int = 60


# Global config instance (lazy loaded)
_config: LLMConfig | None = None


def get_config() -> LLMConfig:
    """Get the global LLM configuration instance."""
    global _config
    if _config is None:
        _config = LLMConfig()
    return _config


def reset_config() -> None:
    """Reset the global config (useful for testing)."""
    global _config
    _config = None
