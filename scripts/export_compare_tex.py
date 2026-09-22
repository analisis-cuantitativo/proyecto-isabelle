"""Export the dashboard's /compare matrix as a LaTeX longtable.

One row per exercise, one column per model. Each cell is a symbol:
validated (verified by any run), not validated (attempted, never verified),
or missing (the model has no run on that exercise). Requires the `booktabs`,
`longtable`, `array` and `amssymb` packages in the report's preamble.
"""

from pathlib import Path

import typer

from proyecto_isabelle.analysis.data import display_model_name
from proyecto_isabelle.dashboard.app import _exercise_matrix, _final_passes_by_run
from proyecto_isabelle.sync.repository import SupabaseRepository

DEFAULT_OUT = (
    Path.home() / "Projects/reporte-proyecto-isabelle/tables/comparacion_modelos.tex"
)

VALIDATED = r"$\checkmark$"
NOT_VALIDATED = r"$\times$"
MISSING = "--"

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


def _cell(c: dict) -> str:
    if not c["num_runs"]:
        return MISSING
    return VALIDATED if c["verified"] else NOT_VALIDATED


def render(models: list[str], matrix: list[dict]) -> str:
    n = len(models)
    solved = [sum(1 for r in matrix if r["cells"][i]["verified"]) for i in range(n)]
    header = (
        "Ejercicio & "
        + " & ".join(
            rf"\rotatebox{{60}}{{{_esc(display_model_name(m))}}}" for m in models
        )
        + r" \\"
    )
    lines = [
        "% Generado por scripts/export_compare_tex.py -- no editar a mano.",
        r"\begingroup\small",
        r"\begin{longtable}{>{\raggedright\arraybackslash}p{0.4\textwidth}"
        + "c" * n
        + "}",
        rf"\caption{{Comparación de modelos por ejercicio: {VALIDATED}~validado, "
        rf"{NOT_VALIDATED}~no validado, {MISSING}~sin intentos.}}",
        r"\label{tab:comparacion_modelos} \\",
        r"\toprule",
        header,
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        header,
        r"\midrule",
        r"\endhead",
        r"\midrule",
        rf"\multicolumn{{{n + 1}}}{{r}}{{\emph{{continúa en la página siguiente}}}} \\",
        r"\endfoot",
        r"\midrule",
        "Validados & " + " & ".join(f"{s}/{len(matrix)}" for s in solved) + r" \\",
        r"\bottomrule",
        r"\endlastfoot",
    ]
    for row in matrix:
        lines.append(
            _esc(row["name"])
            + " & "
            + " & ".join(_cell(c) for c in row["cells"])
            + r" \\"
        )
    lines += [r"\end{longtable}", r"\endgroup", ""]
    return "\n".join(lines)


def render_summary(models: list[str], matrix: list[dict]) -> str:
    """Small tabular (validated / not validated / missing per model) for a wraptable."""
    rows = []
    for i, m in enumerate(models):
        cells = [r["cells"][i] for r in matrix]
        ok = sum(1 for c in cells if c["verified"])
        missing = sum(1 for c in cells if not c["num_runs"])
        rows.append(
            rf"{_esc(display_model_name(m))} & {ok} & {len(cells) - ok - missing} & {missing} \\"
        )
    return "\n".join(
        [
            "% Generado por scripts/export_compare_tex.py -- no editar a mano.",
            r"\footnotesize\setlength{\tabcolsep}{4pt}",
            r"\begin{tabular}{lrrr}",
            r"\toprule",
            r"Modelo & Val. & No val. & Sin int. \\",
            r"\midrule",
            *rows,
            r"\bottomrule",
            r"\end{tabular}",
            "",
        ]
    )


def _num(x: float) -> str:
    return f"{round(x):,}".replace(",", r"\,")


def render_tokens(models: list[str], full_rows: list[dict]) -> str:
    """Token spend per model, from each run's final pass (tokens_consumed is cumulative)."""
    finals = _final_passes_by_run(full_rows)
    lines = []
    for i, m in enumerate(models):
        toks = [f["tokens_consumed"] for f in finals if f["model_name"] == m]
        lines.append(
            rf"{_esc(display_model_name(m))} & {len(toks)} & {_num(sum(toks) / len(toks))} \\"
        )
    return "\n".join(
        [
            "% Generado por scripts/export_compare_tex.py -- no editar a mano.",
            r"\footnotesize\setlength{\tabcolsep}{4pt}",
            r"\begin{tabular}{lrr}",
            r"\toprule",
            r"Modelo & Ejec. & Tokens/ejec. \\",
            r"\midrule",
            *lines,
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
            "Benchmark campaign to export (0 = all campaigns pooled). The "
            "published tables came from campaign 1; pass --version 1 to "
            "regenerate them unchanged once campaign 2 has rows."
        ),
    ),
) -> None:
    repo = SupabaseRepository()
    scope = version or None
    rows = repo.list_benchmark_rows(version=scope)
    models, matrix = _exercise_matrix(rows, repo.list_benchmarkable_exercises())
    out.with_name("tokens_modelos.tex").write_text(
        render_tokens(models, repo.list_full_benchmark_rows(version=scope))
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render(models, matrix))
    summary = out.with_name("resumen_modelos.tex")
    summary.write_text(render_summary(models, matrix))
    typer.echo(f"Wrote {summary}")
    typer.echo(f"Wrote {len(matrix)} exercises x {len(models)} models to {out}")


if __name__ == "__main__":
    typer.run(main)
