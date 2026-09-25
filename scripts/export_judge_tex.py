"""Export the LLM-as-a-judge verdicts that are *not* an exact match as a LaTeX longtable.

Reads the local verdict cache (data/analysis/formalization_judge_cache.jsonl),
keeping only verdicts for the runs' *current* verified final passes (the cache
also holds verdicts for superseded passes, which must not be counted). One row
per judged pass whose category isn't ``exact_match``: flagged ones (``faithful=False``) first, then faithful
reformulations. Requires the `booktabs`, `longtable`, `array` and `amssymb`
packages in the report's preamble.
"""

import json
from pathlib import Path

import typer

from proyecto_isabelle.analysis.data import display_model_name
from proyecto_isabelle.analysis.formalization_judge import CACHE_PATH, rows_to_judge
from proyecto_isabelle.sync.repository import SupabaseRepository

DEFAULT_OUT = (
    Path.home() / "Projects/reporte-proyecto-isabelle/tables/juicio_no_exactos.tex"
)

VALIDATED = r"$\checkmark$"
FLAGGED = r"$\times$"

# Display order (flagged first) and Spanish labels.
CATEGORIES = {
    "different_theorem": "Teorema distinto",
    "weaker_than_intended": "M\\'as d\\'ebil",
    "stronger_than_intended": "M\\'as fuerte",
    "equivalent_reformulation": "Reformulaci\\'on equivalente",
}

_ESCAPES = {
    "_": r"\_\allowbreak{}",
    "&": r"\&",
    "%": r"\%",
    "#": r"\#",
    "$": r"\$",
    "{": r"\{",
    "}": r"\}",
    "^": r"\^{}",
    "~": r"\textasciitilde{}",
    "\\": r"\textbackslash{}",
}


def _esc(s: str) -> str:
    return "".join(_ESCAPES.get(c, c) for c in s)


def load_current(version: int | None = None) -> list[dict]:
    """Cached verdicts for the runs' current verified final passes.

    ``version`` scopes to one benchmark campaign (``None`` pools every
    campaign -- see ``formalization_judge.rows_to_judge``).
    """
    current = {
        int(i) for i in rows_to_judge(SupabaseRepository(), version=version)["id"]
    }
    rows = [json.loads(line) for line in CACHE_PATH.read_text().splitlines() if line]
    return [r for r in rows if r["benchmark_id"] in current]


def load_non_exact() -> list[dict]:
    rows = [r for r in load_current() if r["category"] != "exact_match"]
    order = list(CATEGORIES)
    rows.sort(
        key=lambda r: (order.index(r["category"]), r["exercise_name"], r["model_name"])
    )
    return rows


def render(rows: list[dict]) -> str:
    header = r"Ejercicio & Modelo & Categor\'ia & Fiel \\"
    lines = [
        "% Generado por scripts/export_judge_tex.py -- no editar a mano.",
        r"\begingroup\small",
        r"\begin{longtable}{>{\raggedright\arraybackslash}p{0.42\textwidth}"
        r">{\raggedright\arraybackslash}p{0.2\textwidth}"
        r">{\raggedright\arraybackslash}p{0.22\textwidth}c}",
        rf"\caption{{Veredictos del juez (\textit{{LLM-as-a-judge}}) que no son \textit{{exact match}}: "
        rf"{VALIDATED}~fiel, {FLAGGED}~marcado por el juez.}}",
        r"\label{tab:juicio_no_exactos} \\",
        r"\toprule",
        header,
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        header,
        r"\midrule",
        r"\endhead",
        r"\midrule",
        r"\multicolumn{4}{r}{\emph{contin\'ua en la p\'agina siguiente}} \\",
        r"\endfoot",
        r"\bottomrule",
        r"\endlastfoot",
    ]
    for r in rows:
        lines.append(
            " & ".join(
                [
                    _esc(r["exercise_name"]),
                    _esc(display_model_name(r["model_name"])),
                    CATEGORIES[r["category"]],
                    VALIDATED if r["faithful"] else FLAGGED,
                ]
            )
            + r" \\"
        )
    lines += [r"\end{longtable}", r"\endgroup", ""]
    return "\n".join(lines)


def render_fidelity(rows: list[dict]) -> str:
    """Faithful rate per model (same numbers as the analysis report's section (v),
    without the ``self_judged`` column), for a wraptable."""
    by_model: dict[str, list[bool]] = {}
    for r in rows:
        by_model.setdefault(r["model_name"], []).append(r["faithful"])
    stats = sorted(
        ((m, len(v), sum(v)) for m, v in by_model.items()), key=lambda t: t[2] / t[1]
    )
    body = [
        rf"{_esc(display_model_name(m))} & {n} & {k} & {100 * k / n:.1f}\% \\"
        for m, n, k in stats
    ]
    return "\n".join(
        [
            "% Generado por scripts/export_judge_tex.py -- no editar a mano.",
            r"\footnotesize\setlength{\tabcolsep}{4pt}",
            r"\begin{tabular}{lrrr}",
            r"\toprule",
            r"Modelo & Juzgados & Fieles & Tasa \\",
            r"\midrule",
            *body,
            r"\bottomrule",
            r"\end{tabular}",
            "",
        ]
    )


def main(
    out: Path = typer.Option(DEFAULT_OUT, help="Destination .tex file."),
    version: int = typer.Option(
        0,
        help=(
            "Benchmark campaign to export (0 = all campaigns pooled). Pass "
            "--version 2 to scope the fidelity tables to the current campaign."
        ),
    ),
) -> None:
    current = load_current(version=version or None)
    rows = [r for r in current if r["category"] != "exact_match"]
    rows.sort(
        key=lambda r: (
            list(CATEGORIES).index(r["category"]),
            r["exercise_name"],
            r["model_name"],
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    fidelity = out.with_name("fidelidad_modelos.tex")
    fidelity.write_text(render_fidelity(current))
    typer.echo(f"Wrote {fidelity}")
    out.write_text(render(rows))
    flagged = sum(1 for r in rows if not r["faithful"])
    typer.echo(f"Wrote {len(rows)} rows ({flagged} flagged) to {out}")


if __name__ == "__main__":
    typer.run(main)
