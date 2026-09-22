"""Minimal, read-only local dashboard for proof-agent run logs.

Reads the JSONL files `query/run_log.py` writes under `data/run_logs/` — one
file per run, named after the same `run_id` shared with the `benchmark`
Supabase table. No auth, no database access: this is a local dev tool for
watching (or replaying) what a proof-agent run actually did, run via
`scripts/dashboard.py`.
"""

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from fastapi import FastAPI, Request
from fastapi.responses import HTMLResponse
from fastapi.templating import Jinja2Templates

from proyecto_isabelle.sync.repository import SupabaseRepository
from proyecto_isabelle.util import RUN_LOGS_DIR

app = FastAPI(title="Proof Agent Dashboard")
templates = Jinja2Templates(directory=str(Path(__file__).parent / "templates"))

# Lazily created on first use of the /benchmark page: SupabaseRepository's
# constructor signs in against Supabase, so it's kept out of the local-only
# run-log pages and only paid for once, not per request.
_repo: SupabaseRepository | None = None


def _get_repo() -> SupabaseRepository:
    global _repo
    if _repo is None:
        _repo = SupabaseRepository()
    return _repo


def _read_events(path: Path) -> list[dict[str, Any]]:
    events = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            events.append(json.loads(line))
    return events


def _run_summary(path: Path) -> dict[str, Any]:
    events = _read_events(path)
    started = next((e for e in events if e["type"] == "run_started"), {})
    finished = next((e for e in events if e["type"] == "run_finished"), None)
    return {
        "run_id": path.stem,
        "exercise_name": started.get("exercise_name"),
        "model_name": started.get("model_name"),
        "started_at": started.get("ts"),
        "num_checks": sum(1 for e in events if e["type"] == "tool_return"),
        "running": finished is None,
        "verified": finished.get("verified") if finished else None,
        "hit_retry_budget": bool(finished and finished.get("hit_retry_budget")),
    }


def _final_passes_by_run(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """One row per ``run_id``: the highest-``pass_number`` row in that run.

    ``sync.models.Benchmark`` documents that row as the run's final,
    independently-reverified answer — earlier passes are just the agent's
    intermediate ``check_in_isabelle`` attempts and shouldn't count toward
    whether the run "verified".
    """
    by_run: dict[Any, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_run[row["run_id"]].append(row)
    return [max(passes, key=lambda p: p["pass_number"]) for passes in by_run.values()]


def _model_coverage(
    rows: list[dict[str, Any]], total_exercises: int
) -> list[dict[str, Any]]:
    """Per-model coverage/accuracy, one entry per model seen in ``rows``.

    An exercise counts as "attempted" for a model if any run exists for that
    exercise+model pair, and "verified" if any of those runs' final pass
    verified — a model that solved an exercise on a retried run still gets
    credit, since ``get_missing_exercises_by_model`` only re-attempts
    exercises that haven't already produced a row.
    """
    per_model: dict[str, dict[int, bool]] = defaultdict(dict)
    for final in _final_passes_by_run(rows):
        model, exercise_id = final["model_name"], final["exercise_id"]
        per_model[model][exercise_id] = per_model[model].get(
            exercise_id, False
        ) or bool(final["verified"])

    stats = []
    for model, exercises in per_model.items():
        attempted = len(exercises)
        verified = sum(exercises.values())
        stats.append(
            {
                "model_name": model,
                "attempted": attempted,
                "verified": verified,
                "coverage_pct": (
                    round(100 * attempted / total_exercises, 1)
                    if total_exercises
                    else 0.0
                ),
                "accuracy_pct": (
                    round(100 * verified / attempted, 1) if attempted else 0.0
                ),
                "solved_pct": (
                    round(100 * verified / total_exercises, 1)
                    if total_exercises
                    else 0.0
                ),
            }
        )
    return sorted(stats, key=lambda s: s["model_name"])


def _exercise_breakdown(
    rows: list[dict[str, Any]], exercises: list[dict[str, Any]], model_name: str
) -> list[dict[str, Any]]:
    """Per-exercise result for one model: attempted / verified / # of runs."""
    finals = [f for f in _final_passes_by_run(rows) if f["model_name"] == model_name]
    verified_by_exercise: dict[int, bool] = {}
    runs_by_exercise: dict[int, int] = defaultdict(int)
    for f in finals:
        runs_by_exercise[f["exercise_id"]] += 1
        verified_by_exercise[f["exercise_id"]] = verified_by_exercise.get(
            f["exercise_id"], False
        ) or bool(f["verified"])

    breakdown = [
        {
            "name": ex["name"],
            "attempted": ex["id"] in runs_by_exercise,
            "verified": verified_by_exercise.get(ex["id"], False),
            "num_runs": runs_by_exercise.get(ex["id"], 0),
        }
        for ex in exercises
    ]
    return sorted(breakdown, key=lambda b: b["name"])


def _exercise_matrix(
    rows: list[dict[str, Any]], exercises: list[dict[str, Any]]
) -> tuple[list[str], list[dict[str, Any]]]:
    """Exercises × models grid: each cell is attempted / verified / # of runs.

    Same verified-if-any-run-verified rule as ``_exercise_breakdown``, just
    computed for every model at once. Returns the sorted model names (the
    columns) and one row per exercise (sorted by name) whose ``cells`` line
    up with those columns.
    """
    cells: dict[tuple[int, str], dict[str, Any]] = {}
    for f in _final_passes_by_run(rows):
        cell = cells.setdefault(
            (f["exercise_id"], f["model_name"]), {"num_runs": 0, "verified": False}
        )
        cell["num_runs"] += 1
        cell["verified"] = cell["verified"] or bool(f["verified"])

    models = sorted({model for _, model in cells})
    empty = {"num_runs": 0, "verified": False}
    matrix = [
        {
            "name": ex["name"],
            "cells": [cells.get((ex["id"], m), empty) for m in models],
        }
        for ex in sorted(exercises, key=lambda ex: ex["name"])
    ]
    return models, matrix


@app.get("/", response_class=HTMLResponse)
def list_runs(request: Request, model: str | None = None) -> HTMLResponse:
    paths = (
        sorted(
            RUN_LOGS_DIR.glob("*.jsonl"), key=lambda p: p.stat().st_mtime, reverse=True
        )
        if RUN_LOGS_DIR.is_dir()
        else []
    )
    runs = [_run_summary(p) for p in paths]
    models = sorted({r["model_name"] for r in runs if r["model_name"]})
    if model:
        runs = [r for r in runs if r["model_name"] == model]
    return templates.TemplateResponse(
        request,
        "list.html.jinja",
        {
            "runs": runs,
            "auto_refresh": any(r["running"] for r in runs),
            "models": models,
            "model": model,
        },
    )


@app.get("/runs/{run_id}", response_class=HTMLResponse)
def show_run(request: Request, run_id: str) -> HTMLResponse:
    path = RUN_LOGS_DIR / f"{run_id}.jsonl"
    if not path.is_file():
        return templates.TemplateResponse(
            request,
            "run.html.jinja",
            {"run_id": run_id, "events": None, "running": False},
        )
    events = _read_events(path)
    running = not any(e["type"] == "run_finished" for e in events)
    return templates.TemplateResponse(
        request,
        "run.html.jinja",
        {"run_id": run_id, "events": events, "running": running},
    )


@app.get("/benchmark", response_class=HTMLResponse)
def show_benchmark(
    request: Request, model: str | None = None, version: int | None = None
) -> HTMLResponse:
    """Aggregate coverage/accuracy over the Supabase `benchmark` table.

    Unlike the run-log pages above, this one talks to Supabase directly —
    the local JSONL logs only cover runs made from this machine, while
    `benchmark` has every pass ever recorded for every model.

    `?version=N` scopes the stats to one benchmark campaign; without it
    every campaign is pooled, which mixes runs made against different agent
    revisions.
    """
    try:
        repo = _get_repo()
        exercises = repo.list_benchmarkable_exercises()
        rows = repo.list_benchmark_rows(version=version)
    except Exception as e:
        return templates.TemplateResponse(
            request,
            "benchmark.html.jinja",
            {
                "error": str(e),
                "stats": [],
                "models": [],
                "model": model,
                "version": version,
                "breakdown": None,
                "total_exercises": 0,
            },
        )

    stats = _model_coverage(rows, total_exercises=len(exercises))
    models = [s["model_name"] for s in stats]
    breakdown = _exercise_breakdown(rows, exercises, model) if model else None

    return templates.TemplateResponse(
        request,
        "benchmark.html.jinja",
        {
            "error": None,
            "stats": stats,
            "models": models,
            "model": model,
            "version": version,
            "breakdown": breakdown,
            "total_exercises": len(exercises),
        },
    )


@app.get("/compare", response_class=HTMLResponse)
def show_compare(request: Request, version: int | None = None) -> HTMLResponse:
    """Exercise-by-exercise comparison: one row per exercise, one column per model.

    `?version=N` scopes the grid to one benchmark campaign (see
    `show_benchmark`).
    """
    context: dict[str, Any] = {
        "error": None,
        "models": [],
        "matrix": [],
        "solved_by_model": [],
        "version": version,
    }
    try:
        repo = _get_repo()
        exercises = repo.list_benchmarkable_exercises()
        rows = repo.list_benchmark_rows(version=version)
    except Exception as e:
        context["error"] = str(e)
        return templates.TemplateResponse(request, "compare.html.jinja", context)

    models, matrix = _exercise_matrix(rows, exercises)
    context.update(
        models=models,
        matrix=matrix,
        solved_by_model=[
            sum(1 for row in matrix if row["cells"][i]["verified"])
            for i in range(len(models))
        ],
    )
    return templates.TemplateResponse(request, "compare.html.jinja", context)
