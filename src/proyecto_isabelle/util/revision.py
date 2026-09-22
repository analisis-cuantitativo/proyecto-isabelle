"""The git revision the proof agent is running at.

Recorded on every `benchmark` row from campaign 2 onward (see
`sql/migrations/0002_add_version_to_benchmark.sql`). The first campaign's
headline caveat was that models didn't all face the same Isabelle interface;
stamping each pass with the revision that produced it turns "they ran under
the same conditions" into something a query can confirm.

Both repositories matter: the agent scaffolding lives here, but the Isabelle
interface it talks to is DeepIsaHOL (a submodule), and it was a change on
*that* side that advantaged one model in the first campaign.
"""

from __future__ import annotations

import subprocess

from proyecto_isabelle.util.constants import ROOT_DIR

DEEPISAHOL_DIR = ROOT_DIR / "DeepIsaHOL"


def _describe(repo_dir) -> str:
    """``<short sha>`` for ``repo_dir``, with ``-dirty`` appended if the
    working tree has uncommitted changes. ``unknown`` if it isn't a git
    checkout (e.g. a source tarball, or the submodule never initialized).
    """
    try:
        sha = subprocess.run(
            ["git", "-C", str(repo_dir), "rev-parse", "--short", "HEAD"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError, OSError):
        return "unknown"

    dirty = subprocess.run(
        ["git", "-C", str(repo_dir), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    return f"{sha}-dirty" if dirty.stdout.strip() else sha


def current_agent_revision() -> str:
    """``"proyecto-isabelle@<sha>+DeepIsaHOL@<sha>"`` for the code about to run.

    A ``-dirty`` suffix on either half means that checkout had uncommitted
    changes when the run started, i.e. the revision doesn't fully identify
    what ran -- worth noticing before a campaign, not worth aborting over
    (the run is still more reproducible with an approximate stamp than with
    none at all).
    """
    return (
        f"proyecto-isabelle@{_describe(ROOT_DIR)}"
        f"+DeepIsaHOL@{_describe(DEEPISAHOL_DIR)}"
    )
