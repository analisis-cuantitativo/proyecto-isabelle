"""Useful constants for the project"""

from pathlib import Path
from enum import StrEnum

ROOT_DIR = Path(__file__).parent.parent.parent.parent
PROOFS_DIR = ROOT_DIR / "data" / "proofs"
RUN_LOGS_DIR = ROOT_DIR / "data" / "run_logs"
ANALYSIS_DIR = ROOT_DIR / "data" / "analysis"


class Models(StrEnum):
    """Models available for the benchmark, as pydantic_ai ``"<provider>:<model>"``
    strings — the same convention ``pydantic_ai.models.infer_model`` uses.

    The provider prefix (before the ``:``) must be one ``query.proof_agent``
    knows how to authenticate — see ``proof_agent._PROVIDER_API_KEY_FIELDS``.
    Adding a new provider here means adding one entry there (and an API key
    field on ``LLMConfig``); no other routing code needs to change.
    """

    # Claude model info: https://platform.claude.com/docs/en/about-claude/model-deprecations
    FABLE_5_1 = "anthropic:claude-fable-5-1"
    HAIKU_5 = "anthropic:claude-haiku-4-5-20251001"
    SONNET_4_6 = "anthropic:claude-sonnet-4-6"
    SONNET_4 = "anthropic:claude-sonnet-4-20250514"
    SONNET_4_5 = "anthropic:claude-sonnet-4-5-20250929"
    OPUS_4 = "anthropic:claude-opus-4-20250514"
    OPUS_4_1 = "anthropic:claude-opus-4-1-20250805"
    OPUS_4_5 = "anthropic:claude-opus-4-5-20251101"
    OPUS_4_6 = "anthropic:claude-opus-4-6"
    GPT_6_ASTRA = "openai:gpt-6-astra"
    GPT_5_1_ = "openai:gpt-5-1-sol"
    # The GPT-5.6 family 400s on function-tool requests over the Chat
    # Completions API (/v1/chat/completions) unless reasoning_effort='none'
    # — which disables reasoning outright. The Responses API doesn't have
    # that restriction, hence the "openai-responses" (not "openai") prefix.
    GPT_5_6_TERRA = "openai-responses:gpt-5.6-terra"
    GPT_5_6_LUNA = "openai-responses:gpt-5.6-luna"
    GEMINI_3_8 = "google-gla:gemini-3-8-flash"
    GEMINI_3_6 = "google-gla:gemini-3-6-flash"
    GEMINI_3_5 = "google-gla:gemini-3-5-flash-lite"
    GEMINI_3_1 = "google-gla:gemini-3-1-pro"
    # DeepSeek's API only exposes these two model names (pydantic_ai's
    # DeepSeekProvider types this as Literal["deepseek-chat", "deepseek-reasoner"]).
    DEEPSEEK_CHAT = "deepseek:deepseek-chat"
    DEEPSEEK_REASONER = "deepseek:deepseek-reasoner"
    # Moonshot/Kimi — pydantic_ai doesn't type-constrain these names; double
    # check the exact slug against Moonshot's docs before relying on it.
    KIMI_K3 = "moonshotai:kimi-k3"
    KIMI_K2_6 = "moonshotai:kimi-k2_6"
    KIMI_K2 = "moonshotai:kimi-k2"
