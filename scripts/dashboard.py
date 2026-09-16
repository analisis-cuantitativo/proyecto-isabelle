"""Serve the local dashboard for browsing proof-agent run logs.

Reads the JSONL files under `data/run_logs/` (written by `query/run_log.py`
during `scripts/run.py` runs). Local, read-only, no auth — see
`dashboard/app.py`.
"""

import typer
import uvicorn

app = typer.Typer()


@app.command()
def serve(
    host: str = typer.Option("127.0.0.1", help="Host to bind to."),
    port: int = typer.Option(8321, help="Port to bind to."),
    reload: bool = typer.Option(False, help="Auto-reload on code changes."),
) -> None:
    """Run the dashboard web server."""
    uvicorn.run(
        "proyecto_isabelle.dashboard.app:app",
        host=host,
        port=port,
        reload=reload,
    )


if __name__ == "__main__":
    app()
