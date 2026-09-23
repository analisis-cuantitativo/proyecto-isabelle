"""Incremental, per-run JSONL log of a proof-agent's interactions.

``prove_exercise`` drives the agent via ``Agent.iter()`` instead of the
simpler ``Agent.run()`` specifically so this module can observe (and persist)
every node — model thinking, text, tool calls, tool returns — as it happens,
not just the final result. Each event is written and flushed immediately, so
a run can be tailed (e.g. by the dashboard) while it's still in progress,
not only replayed after it finishes.

One file per run, named after the same ``run_id`` shared with the `benchmark`
Supabase table, so a row there and a log here always refer to the same run.
"""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from uuid import UUID

from pydantic_ai import Agent, CallToolsNode, ModelRequestNode
from pydantic_ai.messages import (
    RetryPromptPart,
    TextPart,
    ThinkingPart,
    ToolCallPart,
    ToolReturnPart,
)

from proyecto_isabelle.util import RUN_LOGS_DIR


def _default(value: Any) -> Any:
    if isinstance(value, datetime):
        return value.isoformat()
    return str(value)


class RunLogWriter:
    """Appends one JSON object per line to ``data/run_logs/<run_id>.jsonl``."""

    def __init__(self, run_id: UUID) -> None:
        self.run_id = run_id
        self.path: Path = RUN_LOGS_DIR / f"{run_id}.jsonl"
        self.path.parent.mkdir(parents=True, exist_ok=True)

    def log_event(self, event: dict[str, Any]) -> None:
        event.setdefault("ts", datetime.now(tz=timezone.utc).isoformat())
        with self.path.open("a") as f:
            f.write(json.dumps(event, default=_default) + "\n")
            f.flush()

    def log_started(
        self,
        exercise_name: str,
        model_name: str,
        max_isabelle_checks: int,
        exercise_statement: str | None = None,
        proof: str | None = None,
        max_isabelle_queries: int | None = None,
        version: int | None = None,
        agent_revision: str | None = None,
    ) -> None:
        """Open the log with the run's fixed facts.

        ``version``/``agent_revision`` are the same campaign and revision the
        run's `benchmark` rows get stamped with (see
        ``SupabaseRepository.save_benchmark_pass``), repeated here so a log
        file says on its own which campaign it belongs to — otherwise the
        only way to place a run is to go back to Supabase and look up its
        ``run_id``. Both default to ``None`` because logs written before this
        existed simply don't have them, and a reader has to tell "not
        recorded" apart from a real campaign.
        """
        self.log_event(
            {
                "type": "run_started",
                "exercise_name": exercise_name,
                "model_name": model_name,
                "max_isabelle_checks": max_isabelle_checks,
                "max_isabelle_queries": max_isabelle_queries,
                "version": version,
                "agent_revision": agent_revision,
                "exercise_statement": exercise_statement,
                "proof": proof,
            }
        )

    def log_node(self, node: object) -> None:
        """Turn one node yielded by ``agent.iter()`` into zero or more events."""
        if Agent.is_call_tools_node(node):
            assert isinstance(node, CallToolsNode)
            response = node.model_response
            for part in response.parts:
                if isinstance(part, ThinkingPart):
                    self.log_event(
                        {
                            "type": "thinking",
                            "content": part.content,
                            "ts": response.timestamp,
                        }
                    )
                elif isinstance(part, TextPart):
                    self.log_event(
                        {
                            "type": "text",
                            "content": part.content,
                            "ts": response.timestamp,
                        }
                    )
                elif isinstance(part, ToolCallPart):
                    self.log_event(
                        {
                            "type": "tool_call",
                            "tool_name": part.tool_name,
                            "args": part.args,
                            "ts": response.timestamp,
                        }
                    )
        elif Agent.is_model_request_node(node):
            assert isinstance(node, ModelRequestNode)
            request = node.request
            for part in request.parts:
                if isinstance(part, ToolReturnPart):
                    self.log_event(
                        {
                            "type": "tool_return",
                            "tool_name": part.tool_name,
                            "content": part.content,
                            "ts": part.timestamp,
                        }
                    )
                elif isinstance(part, RetryPromptPart):
                    self.log_event(
                        {
                            "type": "retry",
                            "tool_name": part.tool_name,
                            "content": part.content,
                            "ts": part.timestamp,
                        }
                    )

    def log_finished(self, **fields: Any) -> None:
        self.log_event({"type": "run_finished", **fields})
