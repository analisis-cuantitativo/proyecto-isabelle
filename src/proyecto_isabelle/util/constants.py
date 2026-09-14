"""Useful constants for the project"""

from pathlib import Path
from enum import StrEnum

MODELS = [
    # Claude model's info:
    # https://platform.claude.com/docs/en/about-claude/model-deprecations
    "anthropic/claude-haiku-4-5-20251001",
    "anthropic/claude-sonnet-4-6",
    "anthropic/claude-sonnet-4-20250514",
    "anthropic/claude-sonnet-4-5-20250929",
    "anthropic/claude-sonnet-4-6",
    "anthropic/claude-opus-4-20250514",
    "anthropic/claude-opus-4-1-20250805",
    "anthropic/claude-opus-4-5-20251101",
    "anthropic/claude-opus-4-6",
]

ROOT_DIR = Path(__file__).parent.parent.parent.parent
PROOFS_DIR = ROOT_DIR / "data" / "proofs"


class Models(StrEnum):
    FABLE_5_1 = "anthropic/claude-fable-5-1"
    HAIKU_5 = "anthropic/claude-haiku-4-5-20251001"
    SONNET_4_6 = "anthropic/claude-sonnet-4-6"
    SONNET_4 = "anthropic/claude-sonnet-4-20250514"
    SONNET_4_5 = "anthropic/claude-sonnet-4-5-20250929"
    OPUS_4 = "anthropic/claude-opus-4-20250514"
    OPUS_4_1 = "anthropic/claude-opus-4-1-20250805"
    OPUS_4_5 = "anthropic/claude-opus-4-5-20251101"
    OPUS_4_6 = "anthropic/claude-opus-4-6"
    GPT_6_ASTRA = "openai/gpt-6-astra"
    GPT_5_1_ = "openai/gpt-5-1-sol"
    GEMINI_3_8 = "google/gemini-3-8-flash"
    GEMINI_3_6 = "google/gemini-3-6-flash"
    GEMINI_3_5 = "google/gemini-3-5-flash-lite"
    GEMINI_3_1 = "google/gemini-3-1-pro"
    DEEPSEEK_V4_PRO = "deepseek/deepseek-v4-pro"
    DEEPSEEK_V4_FLASH = "deepseek/deepseek-v4-flash"
    DEEPSEEK_R1 = "deepseek/deepseek-r1"
    DEEPSEEK_V3 = "deepseek/deepseek-v3"
    KIMI_K3 = "kimi/kimi-k3"
    KIMI_K2_6 = "kimi/kimi-k2_6"
    KIMI_K2 = "kimi/kimi-k2"
