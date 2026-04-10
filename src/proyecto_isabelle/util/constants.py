"""Useful constants for the project"""

from pathlib import Path

MODELS = [
    # Claude model's info:
    # https://platform.claude.com/docs/en/about-claude/model-deprecations
    "claude-haiku-4-5-20251001",
    "claude-sonnet-4-6",
    "claude-sonnet-4-20250514",
    "claude-sonnet-4-5-20250929",
    "claude-sonnet-4-6",
    "claude-opus-4-20250514",
    "claude-opus-4-1-20250805",
    "claude-opus-4-5-20251101",
    "claude-opus-4-6",
]

ROOT_DIR = Path(__file__).parent.parent.parent.parent
