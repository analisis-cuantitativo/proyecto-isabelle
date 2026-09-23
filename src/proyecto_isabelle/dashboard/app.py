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
from proyecto_isabelle.util import BENCHMARK_VERSION, RUN_LOGS_DIR

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


ALL_CAMPAIGNS = "all"
"""``?version=all`` — pool every campaign instead of scoping to one."""


def _selected_version(raw: str | None, default: int | None) -> int | None:
    """Parse the ``?version=`` query parameter into a campaign to scope to.

    ``None`` out means "pool every campaign", which the caller's ``default``
    can also ask for: the benchmark/compare pages default to the current
    campaign (pooling would average results produced under different agent
    revisions), while the run-log list defaults to pooled because local logs
    predating `version` have no campaign at all and shouldn't vanish.

    Anything unparsable falls back to ``default`` rather than erroring —
    this is a local dev tool, and the rendered page always states which
    campaign it ended up showing.
    """
    if raw is None:
        return default
    if raw.strip().lower() == ALL_CAMPAIGNS:
        return None
    try:
        return int(raw)
    except ValueError:
        return default


def _version_arg(version: int | None) -> str:
    """``"version=2"`` / ``"version=all"``, for building links that keep the
    current campaign selected. Always a real value, never empty: a link that
    dropped the parameter would silently fall back to the page's default and
    quietly switch campaigns mid-navigation.
    """
    return f"version={version if version is not None else ALL_CAMPAIGNS}"


def _campaigns(
    rows: list[dict[str, Any]], always_include: tuple[int, ...] = ()
) -> list[dict[str, Any]]:
    """One summary per benchmark campaign found in ``rows``, newest first.

    Answers the questions you ask *before* trusting a rate: how much data a
    campaign has (passes/runs/models/exercises), when it ran, and — the
    point of `benchmark.agent_revision` — whether every pass in it came from
    the same code. More than one revision in a campaign means the models
    didn't all face the same Isabelle interface, which is exactly the flaw
    campaign 2 exists to fix, so the pages surface it rather than leaving it
    to a manual `select distinct`.

    ``always_include`` lists campaigns to summarize even with no rows, so an
    empty-but-current campaign still appears in the picker (a campaign that
    has been prepared but not yet run is a normal state, and hiding it makes
    the dashboard look broken).

    ``created_at`` values are compared as strings: Supabase returns them as
    UTC ISO-8601, where lexicographic and chronological order agree.
    """

    def blank(version: int) -> dict[str, Any]:
        return {
            "version": version,
            "passes": 0,
            "run_ids": set(),
            "model_names": set(),
            "exercise_ids": set(),
            "agent_revisions": set(),
            "first_at": None,
            "last_at": None,
        }

    acc: dict[int, dict[str, Any]] = {v: blank(v) for v in always_include}
    for row in rows:
        campaign = acc.setdefault(row["version"], blank(row["version"]))
        campaign["passes"] += 1
        campaign["run_ids"].add(row["run_id"])
        campaign["model_names"].add(row["model_name"])
        campaign["exercise_ids"].add(row["exercise_id"])
        if row.get("agent_revision"):
            campaign["agent_revisions"].add(row["agent_revision"])
        created_at = row.get("created_at")
        if created_at:
            campaign["first_at"] = min(campaign["first_at"] or created_at, created_at)
            campaign["last_at"] = max(campaign["last_at"] or created_at, created_at)

    return [
        {
            "version": c["version"],
            "passes": c["passes"],
            "runs": len(c["run_ids"]),
            "models": sorted(c["model_names"]),
            "exercises": len(c["exercise_ids"]),
            "agent_revisions": sorted(c["agent_revisions"]),
            # A "-dirty" stamp means that pass ran from a working tree with
            # uncommitted changes, so its revision doesn't actually identify
            # the code that produced it -- worth flagging where the campaign
            # is being read, not just warned about where it was run.
            "has_dirty_revision": any("-dirty" in r for r in c["agent_revisions"]),
            "first_at": c["first_at"],
            "last_at": c["last_at"],
            "is_current": c["version"] == BENCHMARK_VERSION,
        }
        for c in sorted(acc.values(), key=lambda c: c["version"], reverse=True)
    ]


def _campaign_context(repo: SupabaseRepository, version: int | None) -> dict[str, Any]:
    """Shared campaign block for the Supabase-backed pages: every campaign
    that exists, plus the summary of the selected one (``None`` when pooling,
    or when the selected campaign has no rows yet).
    """
    campaigns = _campaigns(
        repo.list_campaign_rows(),
        always_include=(BENCHMARK_VERSION,)
        + ((version,) if version is not None else ()),
    )
    selected = next((c for c in campaigns if c["version"] == version), None)
    return {
        "campaigns": campaigns,
        "campaign": selected,
        "current_version": BENCHMARK_VERSION,
    }


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
        # Both are absent from logs written before `run_started` recorded
        # them, which is most of campaign 1 — `None` there means "not
        # recorded", not "no campaign", and the templates say so.
        "version": started.get("version"),
        "agent_revision": started.get("agent_revision"),
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


# Ordered by how much a reader needs to see it, and used as the sort key for
# the per-exercise table. A regression is what you opened this page for;
# "not re-attempted" goes last because a campaign still in progress has one
# of those for every exercise it hasn't reached yet, and hundreds of them
# above the real results would bury the handful that changed.
CHANGE_ORDER = (
    "regressed",
    "fixed",
    "only_b",
    "stable_failed",
    "stable_verified",
    "only_a",
)


def _results_by_campaign(
    rows: list[dict[str, Any]], model_name: str
) -> dict[int, dict[int, dict[str, Any]]]:
    """``{version: {exercise_id: {verified, num_runs}}}`` for one model.

    Same verified-if-any-run-verified rule as the other pages, applied per
    campaign instead of across all of them — a run's passes all carry one
    ``version``, so grouping by ``run_id`` first (via `_final_passes_by_run`)
    never mixes campaigns within a run.
    """
    per_campaign: dict[int, dict[int, dict[str, Any]]] = defaultdict(dict)
    for final in _final_passes_by_run(rows):
        if final["model_name"] != model_name:
            continue
        results = per_campaign[final["version"]]
        cell = results.setdefault(
            final["exercise_id"], {"verified": False, "num_runs": 0}
        )
        cell["num_runs"] += 1
        cell["verified"] = cell["verified"] or bool(final["verified"])
    return per_campaign


def _campaign_meters(
    results_by_campaign: dict[int, dict[int, dict[str, Any]]], total_exercises: int
) -> list[dict[str, Any]]:
    """Per-campaign solved/attempted/total for one model, newest campaign first.

    Percentages are of *every* benchmarkable exercise, not of what the
    campaign happened to attempt, so the bars are directly comparable: a
    campaign that solved more only because it attempted more doesn't get to
    look like a better model. Accuracy (of what it attempted) is reported
    alongside as a number rather than as a second bar on a second scale.
    """
    meters = []
    for version in sorted(results_by_campaign, reverse=True):
        results = results_by_campaign[version]
        attempted = len(results)
        verified = sum(1 for cell in results.values() if cell["verified"])
        meters.append(
            {
                "version": version,
                "attempted": attempted,
                "verified": verified,
                "total": total_exercises,
                "runs": sum(cell["num_runs"] for cell in results.values()),
                "verified_pct": (
                    round(100 * verified / total_exercises, 1)
                    if total_exercises
                    else 0.0
                ),
                # The bar stacks solved + attempted-but-unsolved, so this is
                # the *unsolved* remainder, not the whole attempted share.
                "unsolved_pct": (
                    round(100 * (attempted - verified) / total_exercises, 1)
                    if total_exercises
                    else 0.0
                ),
                "accuracy_pct": (
                    round(100 * verified / attempted, 1) if attempted else 0.0
                ),
            }
        )
    return meters


def _classify_change(
    before: dict[str, Any] | None, after: dict[str, Any] | None
) -> str:
    if before is None and after is None:
        return "untouched"
    if before is None:
        return "only_b"
    if after is None:
        return "only_a"
    if before["verified"] and not after["verified"]:
        return "regressed"
    if not before["verified"] and after["verified"]:
        return "fixed"
    return "stable_verified" if after["verified"] else "stable_failed"


def _paired_comparison(
    results_by_campaign: dict[int, dict[int, dict[str, Any]]],
    exercises: list[dict[str, Any]],
    a: int,
    b: int,
) -> dict[str, Any]:
    """One model's campaign ``a`` vs campaign ``b``, exercise by exercise.

    The headline is deliberately over the **common subset** — the exercises
    both campaigns actually attempted. Comparing each campaign's overall
    solve count instead would fold a coverage difference into what looks
    like a capability difference: a campaign that only got through half the
    grid before being interrupted would read as a regression. Exercises only
    one campaign touched are still listed (as ``only_a``/``only_b``), just
    kept out of the paired counts.

    Exercises neither campaign attempted are dropped entirely — with ~80 of
    them they'd bury the handful of rows that changed.
    """
    before, after = results_by_campaign.get(a, {}), results_by_campaign.get(b, {})

    rows = []
    counts = dict.fromkeys(CHANGE_ORDER, 0)
    for exercise in exercises:
        change = _classify_change(before.get(exercise["id"]), after.get(exercise["id"]))
        if change == "untouched":
            continue
        counts[change] += 1
        rows.append(
            {
                "name": exercise["name"],
                "before": before.get(exercise["id"]),
                "after": after.get(exercise["id"]),
                "change": change,
            }
        )

    common = [e["id"] for e in exercises if e["id"] in before and e["id"] in after]
    return {
        "a": a,
        "b": b,
        "rows": sorted(
            rows, key=lambda r: (CHANGE_ORDER.index(r["change"]), r["name"])
        ),
        "counts": counts,
        "common": len(common),
        "solved_a": sum(1 for i in common if before[i]["verified"]),
        "solved_b": sum(1 for i in common if after[i]["verified"]),
    }


@app.get("/", response_class=HTMLResponse)
def list_runs(
    request: Request, model: str | None = None, version: str | None = None
) -> HTMLResponse:
    """The local run logs, newest first.

    Unlike `/benchmark` and `/compare`, this defaults to *every* campaign:
    it's a chronological feed of what this machine ran, and runs logged
    before `run_started` recorded a campaign would otherwise disappear from
    it entirely. `?version=N` narrows it to one campaign.
    """
    paths = (
        sorted(
            RUN_LOGS_DIR.glob("*.jsonl"), key=lambda p: p.stat().st_mtime, reverse=True
        )
        if RUN_LOGS_DIR.is_dir()
        else []
    )
    runs = [_run_summary(p) for p in paths]
    models = sorted({r["model_name"] for r in runs if r["model_name"]})
    versions = sorted({r["version"] for r in runs if r["version"] is not None})
    selected_version = _selected_version(version, default=None)
    if model:
        runs = [r for r in runs if r["model_name"] == model]
    if selected_version is not None:
        runs = [r for r in runs if r["version"] == selected_version]
    return templates.TemplateResponse(
        request,
        "list.html.jinja",
        {
            "runs": runs,
            "auto_refresh": any(r["running"] for r in runs),
            "models": models,
            "model": model,
            "versions": versions,
            "version": selected_version,
            # Only propagate a campaign this page was actually asked for:
            # this page's "all" is a default, not a choice, and pushing it
            # into the nav links would silently switch /benchmark and
            # /compare into pooled mode just by navigating there.
            "version_arg": (
                _version_arg(selected_version) if selected_version is not None else ""
            ),
            "current_version": BENCHMARK_VERSION,
        },
    )


@app.get("/runs/{run_id}", response_class=HTMLResponse)
def show_run(request: Request, run_id: str) -> HTMLResponse:
    path = RUN_LOGS_DIR / f"{run_id}.jsonl"
    if not path.is_file():
        return templates.TemplateResponse(
            request,
            "run.html.jinja",
            {
                "run_id": run_id,
                "events": None,
                "running": False,
                "version": None,
                "agent_revision": None,
                "current_version": BENCHMARK_VERSION,
            },
        )
    events = _read_events(path)
    running = not any(e["type"] == "run_finished" for e in events)
    started = next((e for e in events if e["type"] == "run_started"), {})
    return templates.TemplateResponse(
        request,
        "run.html.jinja",
        {
            "run_id": run_id,
            "events": events,
            "running": running,
            "version": started.get("version"),
            "agent_revision": started.get("agent_revision"),
            "current_version": BENCHMARK_VERSION,
        },
    )


@app.get("/benchmark", response_class=HTMLResponse)
def show_benchmark(
    request: Request, model: str | None = None, version: str | None = None
) -> HTMLResponse:
    """Aggregate coverage/accuracy over the Supabase `benchmark` table.

    Unlike the run-log pages above, this one talks to Supabase directly —
    the local JSONL logs only cover runs made from this machine, while
    `benchmark` has every pass ever recorded for every model.

    Scoped to one benchmark campaign: `?version=N` picks one, and the
    default is the campaign new runs are being written under
    (`util.BENCHMARK_VERSION`). `?version=all` pools every campaign, which
    mixes runs made against different agent revisions — the page says so
    rather than quietly reporting the pooled rate as if it were one number.
    """
    selected_version = _selected_version(version, default=BENCHMARK_VERSION)
    context: dict[str, Any] = {
        "error": None,
        "stats": [],
        "models": [],
        "model": model,
        "version": selected_version,
        "version_arg": _version_arg(selected_version),
        "campaigns": [],
        "campaign": None,
        "current_version": BENCHMARK_VERSION,
        "breakdown": None,
        "total_exercises": 0,
    }
    try:
        repo = _get_repo()
        context.update(_campaign_context(repo, selected_version))
        exercises = repo.list_benchmarkable_exercises()
        rows = repo.list_benchmark_rows(version=selected_version)
    except Exception as e:
        context["error"] = str(e)
        return templates.TemplateResponse(request, "benchmark.html.jinja", context)

    stats = _model_coverage(rows, total_exercises=len(exercises))
    context.update(
        stats=stats,
        models=[s["model_name"] for s in stats],
        breakdown=_exercise_breakdown(rows, exercises, model) if model else None,
        total_exercises=len(exercises),
    )
    return templates.TemplateResponse(request, "benchmark.html.jinja", context)


@app.get("/compare", response_class=HTMLResponse)
def show_compare(request: Request, version: str | None = None) -> HTMLResponse:
    """Exercise-by-exercise comparison: one row per exercise, one column per model.

    Campaign-scoped exactly like `show_benchmark`, and for a sharper reason:
    a pooled grid can show two models as both "verified" on an exercise when
    they were actually attempted in different campaigns, under different
    agent revisions — which is precisely the comparison this page exists to
    make trustworthy.
    """
    selected_version = _selected_version(version, default=BENCHMARK_VERSION)
    context: dict[str, Any] = {
        "error": None,
        "models": [],
        "matrix": [],
        "solved_by_model": [],
        "version": selected_version,
        "version_arg": _version_arg(selected_version),
        "campaigns": [],
        "campaign": None,
        "current_version": BENCHMARK_VERSION,
    }
    try:
        repo = _get_repo()
        context.update(_campaign_context(repo, selected_version))
        exercises = repo.list_benchmarkable_exercises()
        rows = repo.list_benchmark_rows(version=selected_version)
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


@app.get("/model-history", response_class=HTMLResponse)
def show_model_history(
    request: Request,
    model: str | None = None,
    a: str | None = None,
    b: str | None = None,
) -> HTMLResponse:
    """One model across every campaign: what changed between two of them.

    The campaign-scoped pages answer "how is this model doing"; this one
    answers "what did re-running under new conditions actually change for
    it" — which exercises it newly solves, which it stopped solving, and
    whether the two campaigns are even comparable (same agent revision?
    overlapping exercise sets?).

    `?a=`/`?b=` pick the two campaigns to diff; they default to the two most
    recent the model has rows in, oldest as `a`, so the page reads
    before → after.
    """
    context: dict[str, Any] = {
        "error": None,
        "models": [],
        "model": model,
        "meters": [],
        "comparison": None,
        "campaigns": [],
        "campaign": None,
        "current_version": BENCHMARK_VERSION,
        "a": None,
        "b": None,
        "versions": [],
        "change_order": CHANGE_ORDER,
    }
    try:
        repo = _get_repo()
        context.update(_campaign_context(repo, None))
        exercises = repo.list_benchmarkable_exercises()
        # Every campaign, on purpose: this page's whole job is the
        # cross-campaign view, so it's the one place pooling the read is
        # right — the campaigns are separated below, not averaged.
        rows = repo.list_benchmark_rows()
    except Exception as e:
        context["error"] = str(e)
        return templates.TemplateResponse(request, "model_history.html.jinja", context)

    context["models"] = sorted({row["model_name"] for row in rows})
    context["campaign"] = None
    if model is None:
        return templates.TemplateResponse(request, "model_history.html.jinja", context)

    results = _results_by_campaign(rows, model)
    versions = sorted(results, reverse=True)
    # Default to the newest two campaigns this model has data in, oldest
    # first: a comparison the reader didn't ask to orient reads as
    # before -> after, not after -> before.
    selected_b = _selected_version(b, default=versions[0] if versions else None)
    selected_a = _selected_version(
        a, default=versions[1] if len(versions) > 1 else None
    )
    context.update(
        meters=_campaign_meters(results, total_exercises=len(exercises)),
        versions=versions,
        a=selected_a,
        b=selected_b,
    )
    if selected_a is not None and selected_b is not None and selected_a != selected_b:
        context["comparison"] = _paired_comparison(
            results, exercises, selected_a, selected_b
        )
    return templates.TemplateResponse(request, "model_history.html.jinja", context)
