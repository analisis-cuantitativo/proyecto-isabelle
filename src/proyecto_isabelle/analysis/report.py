"""Builds the benchmark analysis report: a Markdown write-up plus PNG figures
under ``data/analysis/reports/<timestamp>/``, covering the four questions
this package exists to answer -- per-exercise difficulty, per-topic model
specialization, token consumption (and its correlation with difficulty), and
common Isabelle failure modes ("lessons learned").

Run via ``scripts/analyze_benchmark.py``.
"""

from __future__ import annotations

import matplotlib

matplotlib.use("Agg")

from dataclasses import dataclass  # noqa: E402
from datetime import datetime, timezone  # noqa: E402
from pathlib import Path  # noqa: E402

import matplotlib.pyplot as plt  # noqa: E402
import pandas as pd  # noqa: E402
import seaborn as sns  # noqa: E402
from matplotlib.ticker import FuncFormatter  # noqa: E402

from proyecto_isabelle.analysis import difficulty as difficulty_mod  # noqa: E402
from proyecto_isabelle.analysis import errors as errors_mod  # noqa: E402
from proyecto_isabelle.analysis import formalization_judge  # noqa: E402
from proyecto_isabelle.analysis import integrity as integrity_mod  # noqa: E402
from proyecto_isabelle.analysis import tokens as tokens_mod  # noqa: E402
from proyecto_isabelle.analysis import topics as topics_mod  # noqa: E402
from proyecto_isabelle.analysis.data import (
    display_model_name,
    final_passes,
    load_benchmark_passes,
    load_exercises,
)  # noqa: E402
from proyecto_isabelle.sync.repository import SupabaseRepository  # noqa: E402
from proyecto_isabelle.util import ANALYSIS_DIR  # noqa: E402

_FIGURE_DPI = 150

# Light grid on a white background, print-sized fonts and a colorblind-safe
# palette: legible when the figures are dropped into the (B/W-printable) report.
sns.set_theme(style="whitegrid", context="paper", palette="colorblind", font_scale=1.2)
_MIN_TOPIC_ATTEMPTS = 1
# The topic heatmap needs a stricter floor: at 1 exercise there are ~170 topics
# (mostly 0/1 or 1/1) and ranking them is mostly ties.
_MIN_HEATMAP_EXERCISES = 2
_HEATMAP_TOP_N = 15  # topics per heatmap (easiest / hardest)
_TOP_N = 15


@dataclass
class ReportPaths:
    root: Path
    figures: Path
    report_md: Path


def _new_report_paths() -> ReportPaths:
    stamp = datetime.now(tz=timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    root = ANALYSIS_DIR / "reports" / stamp
    figures = root / "figures"
    figures.mkdir(parents=True, exist_ok=True)
    return ReportPaths(root=root, figures=figures, report_md=root / "report.md")


def _md_table(df: pd.DataFrame) -> str:
    return df.to_markdown(index=False, floatfmt=".2f")


# --- figures -----------------------------------------------------------


def _fig_difficulty_hist(path: Path, stats: pd.DataFrame) -> None:
    fig, ax = plt.subplots(figsize=(7, 5))
    ax.hist(stats["model_level_solved_rate"], bins=11, range=(0, 1.0001))
    ax.set_xlabel("Model-level solved rate")
    ax.set_ylabel("Number of exercises")
    ax.set_title("Distribution of exercise difficulty")
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


def _fig_hardest(path: Path, hardest_df: pd.DataFrame) -> None:
    """The hardest slice is mostly (or entirely) a 0% solved rate, which
    would just draw invisible zero-width bars -- plot average passes before
    giving up instead, which still varies within that slice and shows how
    much effort was spent before abandoning each one."""
    fig, ax = plt.subplots(figsize=(9, max(4, len(hardest_df) * 0.35)))
    ax.barh(hardest_df["name"], hardest_df["avg_passes_to_final"])
    ax.invert_yaxis()
    ax.set_xlabel("Average passes before giving up")
    ax.set_title("Hardest exercises (lowest solved rate)")
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


def _fig_easiest(path: Path, easiest_df: pd.DataFrame) -> None:
    fig, ax = plt.subplots(figsize=(9, max(4, len(easiest_df) * 0.35)))
    ax.barh(easiest_df["name"], easiest_df["avg_passes_to_final"])
    ax.invert_yaxis()
    ax.set_xlabel("Intentos promedio hasta la respuesta final (menos = más trivial)")
    ax.set_title("Ejercicios más fáciles")
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


def _fig_topic_heatmap(path: Path, topic_acc: pd.DataFrame, title: str) -> None:
    """Topic x model heatmap, one row per topic in the order given (topics as
    rows so the labels stay horizontal). Cells are annotated with
    ``validados/ejercicios`` since the proportion alone hides the small n."""
    order = list(dict.fromkeys(topic_acc["topic"]))
    pivot = topic_acc.pivot(index="topic", columns="model_name", values="accuracy")
    counts = topic_acc.assign(
        label=lambda d: d["verified"].astype(int).astype(str)
        + "/"
        + d["attempts"].astype(str)
    ).pivot(index="topic", columns="model_name", values="label")
    pivot, counts = pivot.loc[order], counts.loc[order, pivot.columns]
    pivot.columns = counts.columns = [display_model_name(m) for m in pivot.columns]
    pivot.index = counts.index = [t.replace("_", " ") for t in pivot.index]

    # ~4in wide: meant to sit in a half-width wrapfigure in the report.
    fig, ax = plt.subplots(figsize=(4.0, len(pivot) * 0.27 + 1.7))
    sns.heatmap(
        pivot,
        annot=counts,
        fmt="",
        cmap="viridis",
        vmin=0,
        vmax=1,
        linewidths=0.5,
        linecolor="white",
        annot_kws={"fontsize": 6.5},
        cbar_kws={"label": "Fracción validada", "shrink": 0.6, "pad": 0.03},
        ax=ax,
    )
    ax.grid(False)
    ax.set_xlabel("")
    ax.set_ylabel("")
    ax.tick_params(axis="x", rotation=35, labelsize=7)
    ax.tick_params(axis="y", labelsize=7)
    plt.setp(ax.get_xticklabels(), ha="right")
    ax.figure.axes[-1].tick_params(labelsize=7)
    ax.figure.axes[-1].yaxis.label.set_size(7.5)
    ax.set_title(title, fontsize=9)
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


def _fig_topic_heatmaps(figures: Path, topic_acc: pd.DataFrame) -> None:
    """Two heatmaps: the `_HEATMAP_TOP_N` easiest and hardest topics, ranked by
    the share of validated exercises pooled over every model (ties broken by
    how many exercises back the topic, most first)."""
    pooled = topic_acc.groupby("topic").agg(
        verified=("verified", "sum"), attempts=("attempts", "sum")
    )
    pooled["rate"] = pooled["verified"] / pooled["attempts"]
    easiest = pooled.sort_values(["rate", "attempts"], ascending=[False, False])
    hardest = pooled.sort_values(["rate", "attempts"], ascending=[True, False])
    for name, ranked, title in (
        ("easiest", easiest, "Temas más fáciles"),
        ("hardest", hardest, "Temas más difíciles"),
    ):
        topics = ranked.index[:_HEATMAP_TOP_N]
        subset = topic_acc[topic_acc["topic"].isin(topics)].copy()
        subset["topic"] = pd.Categorical(
            subset["topic"], categories=topics, ordered=True
        )
        _fig_topic_heatmap(
            figures / f"topic_heatmap_{name}.png",
            subset.sort_values("topic").astype({"topic": str}),
            title,
        )


def _fig_tokens_vs_solved(path: Path, tvd: pd.DataFrame) -> None:
    fig, ax = plt.subplots(figsize=(8, 6))
    ax.scatter(tvd["mean_tokens"], tvd["model_level_solved_rate"], alpha=0.6)
    ax.set_xlabel("Mean total tokens consumed (across runs)")
    ax.set_ylabel("Model-level solved rate")
    ax.set_title("Exercise difficulty vs. token spend")
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


def _fig_token_boxplot(path: Path, finals: pd.DataFrame) -> None:
    data = finals.assign(
        Modelo=finals["model_name"].map(display_model_name),
        Resultado=finals["verified"].map({True: "Validado", False: "No validado"}),
    ).sort_values("Modelo")

    fig, ax = plt.subplots(figsize=(8, 5))
    sns.boxplot(
        data=data,
        x="Modelo",
        y="tokens_consumed",
        hue="Resultado",
        hue_order=["Validado", "No validado"],
        showfliers=False,
        ax=ax,
    )
    ax.xaxis.grid(False)
    ax.yaxis.set_major_formatter(
        FuncFormatter(lambda v, _: f"{v:,.0f}".replace(",", " "))
    )
    ax.set_xlabel("")
    ax.set_ylabel("Tokens consumidos por ejecución")
    ax.set_title("Consumo de tokens por modelo, según el resultado de la ejecución")
    ax.legend(title="", loc="upper right")
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


def _fig_error_categories(path: Path, categorized_passes: pd.DataFrame) -> None:
    freq = (
        categorized_passes.groupby(["model_name", "category"])
        .size()
        .unstack(fill_value=0)
    )
    proportions = freq.div(freq.sum(axis=1), axis=0)
    fig, ax = plt.subplots(figsize=(10, 6))
    x = range(len(proportions.index))
    bottoms = [0.0] * len(proportions.index)
    for category in proportions.columns:
        values = proportions[category].to_numpy()
        ax.bar(x, values, bottom=bottoms, label=category)
        bottoms = [b + v for b, v in zip(bottoms, values)]
    ax.set_xticks(list(x))
    ax.set_xticklabels(proportions.index, rotation=20, ha="right")
    ax.set_ylabel("Share of error messages")
    ax.set_title("Isabelle failure-message categories by model")
    ax.legend(bbox_to_anchor=(1.02, 1), loc="upper left", fontsize=8)
    fig.tight_layout()
    fig.savefig(path, dpi=_FIGURE_DPI)
    plt.close(fig)


# --- narrative -----------------------------------------------------------


def _lessons_learned(
    category_freq: pd.DataFrame,
    unresolved: pd.DataFrame,
    specialization_df: pd.DataFrame,
    retry_by_model: pd.DataFrame,
    correlations: dict[str, float],
) -> list[str]:
    bullets: list[str] = []

    if not category_freq.empty:
        totals = (
            category_freq.groupby("category")["count"]
            .sum()
            .sort_values(ascending=False)
        )
        top_category, top_count = totals.index[0], totals.iloc[0]
        share = top_count / totals.sum()
        bullets.append(
            f"The single most common Isabelle failure mode across every model is "
            f"**{top_category}** ({top_count} messages, {share:.0%} of all recorded "
            "errors) -- worth prioritizing in prompt guidance or a retry heuristic."
        )

    if not unresolved.empty:
        for model, group in unresolved.groupby("model_name"):
            top = group.sort_values("count", ascending=False).iloc[0]
            bullets.append(
                f"For **{model}**, the failure mode that most often survives to a run's "
                f"final (unfixed) answer is **{top['category']}** ({int(top['count'])} "
                "runs) -- this is what the model most often fails to recover from within "
                "its retry budget."
            )

    if not specialization_df.empty:
        for model, group in specialization_df.groupby("model_name"):
            best = group.iloc[0]
            worst = group.iloc[-1]
            if best["delta_vs_own_average"] > 0.15:
                bullets.append(
                    f"**{model}** noticeably over-performs its own average on "
                    f"**{best['topic']}** ({best['accuracy']:.0%} vs. its overall "
                    f"{best['model_overall_accuracy']:.0%})."
                )
            if worst["delta_vs_own_average"] < -0.15:
                bullets.append(
                    f"**{model}** noticeably under-performs its own average on "
                    f"**{worst['topic']}** ({worst['accuracy']:.0%} vs. its overall "
                    f"{worst['model_overall_accuracy']:.0%})."
                )

    if not retry_by_model.empty:
        ranked = retry_by_model.sort_values("retries_per_run", ascending=False)
        top = ranked.iloc[0]
        if top["retries_per_run"] > 0.1:
            bullets.append(
                f"**{top['model_name']}** is bounced by the output validator "
                f"(submitting `sorry`/`oops`, or a final answer never run through "
                f"`check_in_isabelle`) {top['retries_per_run']:.2f} times per run on "
                "average, the highest of any model with local run logs -- these retries "
                "never reach Isabelle at all, so they're invisible in `benchmark.errors`."
            )

    pearson = correlations.get("pearson_tokens_vs_solved_rate")
    if pearson is not None and pd.notna(pearson):
        direction = "negatively" if pearson < 0 else "positively"
        strength = (
            "weakly"
            if abs(pearson) < 0.3
            else "moderately"
            if abs(pearson) < 0.6
            else "strongly"
        )
        bullets.append(
            f"Token spend per exercise is {strength} {direction} correlated with solve "
            f"rate (Pearson r={pearson:.2f}) -- "
            + (
                "harder exercises don't simply cost more tokens; something else (missing "
                "library lemmas, ambiguous statement) is driving failure."
                if abs(pearson) < 0.3
                else "models do spend more tokens on exercises they eventually solve, "
                "consistent with iterating productively rather than thrashing."
                if pearson > 0
                else "models spend *more* tokens on exercises they still fail, "
                "consistent with thrashing (retrying without converging) rather than "
                "making productive progress."
            )
        )

    if not bullets:
        bullets.append(
            "Not enough data yet to draw a reliable lesson from any signal above."
        )

    return bullets


def _coverage_table(finals: pd.DataFrame, total_exercises: int) -> pd.DataFrame:
    coverage = (
        finals.groupby("model_name")["exercise_id"]
        .nunique()
        .rename("exercises_attempted")
        .reset_index()
    )
    coverage["coverage_pct"] = round(
        100 * coverage["exercises_attempted"] / total_exercises, 1
    )
    return coverage.sort_values("coverage_pct", ascending=False)


def build_report(min_topic_attempts: int = _MIN_TOPIC_ATTEMPTS) -> ReportPaths:
    paths = _new_report_paths()
    repo = SupabaseRepository()

    passes = load_benchmark_passes(repo)
    exercises = load_exercises(repo)
    finals = final_passes(passes)
    total_exercises = len(exercises)

    # --- naming caveat: historical "<provider>/<model>" rows folded in ---
    renamed = passes.loc[
        passes["model_name_raw"] != passes["model_name"],
        ["model_name_raw", "model_name"],
    ].drop_duplicates()

    # --- data integrity: runs where an earlier pass verified but the final
    # (highest-pass_number) pass didn't, so the run counts as unsolved below
    # despite Isabelle having accepted a proof somewhere in its trace ---
    lost = integrity_mod.lost_verifications(passes)
    lost_classified = integrity_mod.classify_by_content(repo, lost)

    # --- (i) difficulty ---
    diff_stats = difficulty_mod.exercise_difficulty(finals, exercises)
    hardest = difficulty_mod.hardest(diff_stats, n=_TOP_N)
    easiest = difficulty_mod.easiest(diff_stats, n=_TOP_N)
    _fig_difficulty_hist(paths.figures / "difficulty_hist.png", diff_stats)
    _fig_hardest(paths.figures / "hardest_exercises.png", hardest)
    if not easiest.empty:
        _fig_easiest(paths.figures / "easiest_exercises.png", easiest)

    # --- (ii) topic specialization ---
    exploded_topics = topics_mod.explode_topics(finals, exercises)
    topic_acc = topics_mod.topic_model_accuracy(
        exploded_topics, min_attempts=min_topic_attempts
    )
    specialization_df = (
        topics_mod.specialization(topic_acc) if not topic_acc.empty else topic_acc
    )
    if not topic_acc.empty:
        # Count distinct exercises (verified if any run verified), not runs, so
        # reruns don't inflate a cell -- same rule as the model comparison table.
        per_exercise = exploded_topics.groupby(
            ["exercise_id", "model_name", "topic"], as_index=False
        )["verified"].max()
        _fig_topic_heatmaps(
            paths.figures,
            topics_mod.topic_model_accuracy(
                per_exercise, min_attempts=_MIN_HEATMAP_EXERCISES
            ),
        )

    # --- (iii) tokens ---
    token_stats = tokens_mod.token_stats_by_model(finals)
    tvd = tokens_mod.tokens_vs_difficulty(finals, diff_stats)
    correlations = tokens_mod.correlation_summary(tvd)
    _fig_tokens_vs_solved(paths.figures / "tokens_vs_solved_rate.png", tvd)
    _fig_token_boxplot(paths.figures / "tokens_boxplot.png", finals)

    # --- (iv) lessons learned ---
    categorized_passes = errors_mod.categorize_passes(passes)
    category_freq = errors_mod.category_frequency(categorized_passes)
    unresolved = errors_mod.unresolved_categories(passes, categorized_passes)
    if not categorized_passes.empty:
        _fig_error_categories(
            paths.figures / "error_categories.png", categorized_passes
        )

    retry_counts = errors_mod.retry_event_counts(finals["run_id"].astype(str).tolist())
    if not retry_counts.empty:
        run_to_model = finals.set_index(finals["run_id"].astype(str))["model_name"]
        retry_counts["model_name"] = retry_counts["run_id"].map(run_to_model)
        retry_by_model = (
            retry_counts.groupby("model_name")
            .agg(
                runs_with_log=("run_id", "count"), total_retries=("num_retries", "sum")
            )
            .reset_index()
        )
        retry_by_model["retries_per_run"] = (
            retry_by_model["total_retries"] / retry_by_model["runs_with_log"]
        )
    else:
        retry_by_model = pd.DataFrame(
            columns=["model_name", "runs_with_log", "total_retries", "retries_per_run"]
        )

    lessons = _lessons_learned(
        category_freq, unresolved, specialization_df, retry_by_model, correlations
    )

    coverage = _coverage_table(finals, total_exercises)
    full_coverage_models = coverage.loc[
        coverage["exercises_attempted"] == total_exercises, "model_name"
    ].tolist()

    # --- write markdown ---
    lines: list[str] = []
    lines.append(f"# Benchmark analysis report ({paths.root.name})")
    lines.append("")
    lines.append(
        f"Generated from {len(passes)} `benchmark` passes across {finals['run_id'].nunique()} "
        f"runs, {finals['model_name'].nunique()} models, and {total_exercises} benchmarkable "
        "exercises."
    )
    lines.append("")
    if not renamed.empty:
        lines.append(
            "**Note:** the following historical `model_name` spellings were merged into "
            "their canonical form before computing anything below (see "
            "`analysis.data.canonicalize_model_name`):"
        )
        lines.append("")
        lines.append(_md_table(renamed))
        lines.append("")
    lines.append("## Coverage")
    lines.append("")
    lines.append(_md_table(coverage))
    lines.append("")
    if full_coverage_models:
        lines.append(
            "Full-coverage models (every benchmarkable exercise attempted at least once): "
            + ", ".join(f"`{m}`" for m in full_coverage_models)
            + ". Model-vs-model comparisons below are most trustworthy for these; "
            "others reflect a partial, possibly biased sample of exercises."
        )
        lines.append("")

    lines.append("## Data integrity: lost verifications")
    lines.append("")
    if lost.empty:
        lines.append(
            "No run had an earlier pass verify and then a later (final) pass fail -- "
            "every run's highest-`pass_number` row is consistent with its own history."
        )
    else:
        pct = 100 * len(lost) / finals["run_id"].nunique()
        is_probe = lost_classified["last_verified_is_probe"].fillna(False)
        same_mask = lost_classified["same_content"]
        gamed_mask = lost_classified["gamed"]
        flaky_mask = same_mask & ~gamed_mask
        genuine_regression_mask = ~same_mask & ~gamed_mask & ~is_probe
        probe_mask = ~same_mask & ~gamed_mask & is_probe

        flaky_count = int(flaky_mask.sum())
        gamed_count = int(gamed_mask.sum())
        genuine_regression_count = int(genuine_regression_mask.sum())
        probe_count = int(probe_mask.sum())

        by_model = (
            lost_classified.assign(
                flaky_build=flaky_mask,
                gaming_correction=gamed_mask,
                probe_not_a_real_lost_proof=probe_mask,
                genuine_regression=genuine_regression_mask,
            )
            .groupby("model_name")[
                [
                    "flaky_build",
                    "gaming_correction",
                    "probe_not_a_real_lost_proof",
                    "genuine_regression",
                ]
            ]
            .sum()
            .reset_index()
        )
        by_model["really_lost"] = (
            by_model["flaky_build"] + by_model["genuine_regression"]
        )
        worst_model = by_model.sort_values("really_lost", ascending=False).iloc[0]

        lines.append(
            f"Every metric above trusts `benchmark`'s highest-`pass_number` row as a "
            f"run's final answer (see `sync.models.Benchmark`). In **{len(lost)} of "
            f"{finals['run_id'].nunique()} runs ({pct:.1f}%)**, an *earlier* pass "
            "verified but the final pass didn't. The first read of that is "
            '"these runs count as unsolved even though Isabelle accepted a proof '
            'somewhere in the trace" -- diffing `thy_content` shows that is only '
            "true for some of them:"
        )
        lines.append("")
        lines.append(
            f"- **{flaky_count} flaky builds** -- byte-identical `thy_content` "
            "verified once, then failed a fresh rebuild later, with nothing in "
            "the content itself (see `query.isabelle._incomplete_commands`) "
            "explaining why. A build-reliability problem (e.g. resource "
            "contention from concurrent runs), not anything the model did; "
            "these runs really did have a working proof and really did lose "
            "credit for it."
        )
        lines.append(
            f"- **{gamed_count} gaming corrections** -- byte-identical "
            "`thy_content`, but this project *deliberately* re-flagged it as "
            "unverified after finding it gamed verification (an "
            "`axiomatization`-asserted goal, or no `lemma`/`theorem` statement "
            "at all -- see `query.isabelle._incomplete_commands`). Same "
            "same-content signature as a flaky build, but not one: this is a "
            "correction, not something to treat as a lost proof."
        )
        lines.append(
            f"- **{probe_count} probes, not lost proofs** -- the last-verified pass "
            "was `check_in_isabelle` misused for exploration (`find_theorems` "
            'lookups, `thm` citations, or a throwaway `lemma test: "1 + 1 = 2" by '
            "simp`) that happened to build clean, not a real attempt at the "
            "exercise. These runs were never solved in the first place -- the "
            '"lost verification" reading is wrong for this bucket.'
        )
        lines.append(
            f"- **{genuine_regression_count} genuine regressions** -- different, "
            "real content: the model had a working proof and replaced it with "
            "something that doesn't verify. Nothing in `build_proof_agent`'s output "
            "validators pins the final submission to the last verified check."
        )
        lines.append("")
        lines.append(_md_table(by_model))
        lines.append("")
        real_loss_count = flaky_count + genuine_regression_count
        if real_loss_count > 0:
            lines.append(
                "**None of the difficulty/topic/token numbers in this report are "
                f"adjusted for the real losses** (`flaky_build` + "
                f"`genuine_regression` = **{real_loss_count}** runs) -- treat every "
                "solved-rate below as a lower bound, more so for "
                f"`{worst_model['model_name']}` ({int(worst_model['really_lost'])} "
                "affected runs). The probe and gaming-correction runs need no "
                "correction: they were correctly scored as unsolved."
            )
        else:
            lines.append(
                "No real losses remain (every `flaky_build`/`genuine_regression` "
                "case has been corrected in `benchmark` directly, or none existed "
                "this run) -- the difficulty/topic/token numbers below need no "
                "adjustment. The probe and gaming-correction runs above were "
                "correctly scored as unsolved and need none either."
            )
        lines.append("")

    lines.append("## (i) Exercise difficulty")
    lines.append("")
    lines.append("![Difficulty distribution](figures/difficulty_hist.png)")
    lines.append("")
    lines.append("### Hardest exercises")
    lines.append("")
    lines.append("![Hardest exercises](figures/hardest_exercises.png)")
    lines.append("")
    lines.append(
        _md_table(
            hardest[
                [
                    "name",
                    "num_models_attempted",
                    "num_models_that_solved_it",
                    "model_level_solved_rate",
                    "avg_passes_to_final",
                    "retry_budget_hit_rate",
                ]
            ]
        )
    )
    lines.append("")
    if not easiest.empty:
        lines.append("### Easiest / most trivial exercises")
        lines.append("")
        lines.append("![Easiest exercises](figures/easiest_exercises.png)")
        lines.append("")
        lines.append(
            _md_table(
                easiest[
                    [
                        "name",
                        "num_models_attempted",
                        "avg_passes_to_final",
                        "retry_budget_hit_rate",
                    ]
                ]
            )
        )
        lines.append("")

    lines.append("## (ii) Topic specialization")
    lines.append("")
    if topic_acc.empty:
        lines.append(
            f"No (model, topic) pair reached the {min_topic_attempts}-attempt minimum yet."
        )
    else:
        lines.append("![Easiest topics](figures/topic_heatmap_easiest.png)")
        lines.append("")
        lines.append("![Hardest topics](figures/topic_heatmap_hardest.png)")
        lines.append("")
        lines.append(
            f"Most topics tag only 1-2 exercises (of {total_exercises} total), so most "
            f"(model, topic) cells never reach even a {min_topic_attempts}-attempt "
            "minimum and are left blank above -- read any single cell's accuracy as a "
            "rough signal from a handful of attempts, not a stable estimate. Attempt "
            "counts are in the `attempts` column below."
        )
        lines.append("")
        lines.append(
            "Topics where a model's accuracy diverges most from its own average:"
        )
        lines.append("")
        lines.append(
            _md_table(
                pd.concat([specialization_df.head(10), specialization_df.tail(10)])[
                    [
                        "model_name",
                        "topic",
                        "attempts",
                        "accuracy",
                        "model_overall_accuracy",
                        "delta_vs_own_average",
                    ]
                ]
            )
        )
    lines.append("")

    lines.append("## (iii) Token consumption")
    lines.append("")
    lines.append("![Tokens by model](figures/tokens_boxplot.png)")
    lines.append("")
    lines.append(_md_table(token_stats))
    lines.append("")
    lines.append("![Tokens vs. solved rate](figures/tokens_vs_solved_rate.png)")
    lines.append("")
    lines.append(
        "Correlation between an exercise's mean token spend and its difficulty:"
    )
    lines.append("")
    for key, value in correlations.items():
        lines.append(
            f"- `{key}` = {value:.3f}" if pd.notna(value) else f"- `{key}` = n/a"
        )
    lines.append("")

    lines.append("## (iv) Lessons learned")
    lines.append("")
    if not category_freq.empty:
        lines.append("![Error categories by model](figures/error_categories.png)")
        lines.append("")
    for bullet in lessons:
        lines.append(f"- {bullet}")
    lines.append("")

    lines.append("## (v) Formalization fidelity (LLM-as-judge)")
    lines.append("")
    judge_cache = formalization_judge.load_cache_df()
    if not judge_cache.empty:
        # A cached verdict can outlive the row it judged: `analysis.integrity`
        # and the axiomatization/no-statement correction both insert a new
        # final pass for a run without deleting the old one, so a stale
        # `benchmark_id` here no longer belongs to any run's *current*
        # verified final pass and would otherwise double-count against a
        # `total_verified` that's already moved on.
        current_verified_ids = set(finals.loc[finals["verified"], "id"])
        judge_cache = judge_cache.loc[
            judge_cache["benchmark_id"].isin(current_verified_ids)
        ]
    if judge_cache.empty:
        lines.append(
            "Not run yet -- `verified=True` only means Isabelle accepted the proof "
            "for whatever the theory *states*, not that the theory states the "
            "right theorem. Run `scripts/judge_formalizations.py` to check judged "
            "passes against each exercise's natural-language statement."
        )
    else:
        total_verified = len(finals.loc[finals["verified"]])
        rate_table = formalization_judge.faithful_rate_by_model(judge_cache)
        flagged = formalization_judge.flagged_cases(judge_cache)
        self_judged_total = int(judge_cache["self_judged"].sum())

        lines.append(
            f"{len(judge_cache)} of {total_verified} verified final passes judged "
            f"against their exercise's natural-language statement (not the proof "
            "itself, which Isabelle already checked -- only whether the formal "
            "`shows`/`assumes` clause says what the exercise actually asked)."
        )
        lines.append("")
        lines.append(_md_table(rate_table))
        lines.append("")
        if self_judged_total:
            lines.append(
                f"**{self_judged_total} row(s) were judged by the same model that "
                "produced them** (judging was split across models to spread cost "
                "across separate API budgets) -- the `self_judged` count above "
                "flags which models' rates include this self-preference-bias "
                "risk; read those rates with lower confidence than the rest."
            )
            lines.append("")
        if flagged.empty:
            lines.append("No judged pass was flagged as unfaithful to its statement.")
        else:
            lines.append(
                f"**{len(flagged)} judged pass(es) were flagged as not faithful** "
                "to the exercise's statement despite verifying in Isabelle:"
            )
            lines.append("")
            lines.append(
                _md_table(
                    flagged[
                        [
                            "exercise_name",
                            "model_name",
                            "category",
                            "self_judged",
                            "reasoning",
                        ]
                    ]
                )
            )
        lines.append("")

    paths.report_md.write_text("\n".join(lines))
    return paths
