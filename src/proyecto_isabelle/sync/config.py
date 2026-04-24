"""Configuration for GCP Cloud Storage sync using pydantic-settings."""

from pydantic_settings import BaseSettings, SettingsConfigDict


class GCPConfig(BaseSettings):
    """Configuration for GCP Cloud Storage.

    All settings can be configured via environment variables.
    """

    model_config = SettingsConfigDict(
        env_file=".env",
        env_file_encoding="utf-8",
        extra="ignore",
    )

    # GCP bucket name
    gcp_bucket_name: str | None = None


# Global config instance (lazy loaded)
_config: GCPConfig | None = None


def get_config() -> GCPConfig:
    """Get the global GCP configuration instance."""
    global _config
    if _config is None:
        _config = GCPConfig()
    return _config


def reset_config() -> None:
    """Reset the global config (useful for testing)."""
    global _config
    _config = None
