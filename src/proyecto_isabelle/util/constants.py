"""Useful constants for the project"""

from enum import StrEnum
from pathlib import Path

MODELS = [
    # Claude model's info:
    # https://platform.claude.com/docs/en/about-claude/model-deprecations
    "anthropic/claude-haiku-4-5-20251001",
    "anthropic/claude-sonnet-4-6",
    "anthropic/claude-sonnet-4-20250514",
    "anthropic/claude-sonnet-4-5-20250929",
    "anthropic/claude-opus-4-20250514",
    "anthropic/claude-opus-4-1-20250805",
    "anthropic/claude-opus-4-5-20251101",
    "anthropic/claude-opus-4-6",
]

ROOT_DIR = Path(__file__).parent.parent.parent.parent
PROOFS_DIR = ROOT_DIR / "data" / "proofs"


class Models(StrEnum):
    Haiku_5 = "anthropic/claude-haiku-4-5-20251001"
    Sonnet_4_6 = "anthropic/claude-sonnet-4-6"
    Sonnet_4 = "anthropic/claude-sonnet-4-20250514"
    Sonnet_4_5 = "anthropic/claude-sonnet-4-5-20250929"
    opus_4 = "anthropic/claude-opus-4-20250514"
    opus_4_1 = "anthropic/claude-opus-4-1-20250805"
    opus_4_5 = "anthropic/claude-opus-4-5-20251101"
    opus_4_6 = "anthropic/claude-opus-4-6"
