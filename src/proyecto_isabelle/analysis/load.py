# Utilities for loading proof data from hive-partitioned storage.

import duckdb
import pandas as pd

from proyecto_isabelle.util.constants import PROOFS_DIR


def load_proofs(data_dir=None) -> pd.DataFrame:
    """Load all proofs from the hive-partitioned data directory.

    The data is structured as:
        data/proofs/exercise=<name>/model=<model_id>/<hash>.json

    Returns a DataFrame with columns: exercise, model, hash, timestamp,
    verified, errors, raw_response, thinking_budget.
    """
    data_dir = data_dir or PROOFS_DIR
    pattern = str(data_dir / "*/*/*.json")

    query = f"""
    SELECT
        exercise,
        model,
        hash,
        timestamp,
        verified,
        errors,
        raw_response,
        thinking_budget
    FROM read_json(
        '{pattern}',
        hive_partitioning = true
    )
    """
    return duckdb.sql(query).df()


def success_rate_by_model(df: pd.DataFrame | None = None) -> pd.DataFrame:
    """Compute success rate (verified proofs) per model.

    Returns DataFrame with columns: model, total, verified, success_rate.
    """
    if df is None:
        df = load_proofs()

    return duckdb.sql(
        """
        SELECT
            model,
            COUNT(*) as total,
            SUM(CASE WHEN verified THEN 1 ELSE 0 END) as verified,
            ROUND(SUM(CASE WHEN verified THEN 1 ELSE 0 END) * 100.0 / COUNT(*), 2) as success_rate
        FROM df
        GROUP BY model
        ORDER BY success_rate DESC
    """
    ).df()


def success_rate_by_exercise(df: pd.DataFrame | None = None) -> pd.DataFrame:
    """Compute success rate per exercise.

    Returns DataFrame with columns: exercise, total, verified, success_rate.
    """
    if df is None:
        df = load_proofs()

    return duckdb.sql(
        """
        SELECT
            exercise,
            COUNT(*) as total,
            SUM(CASE WHEN verified THEN 1 ELSE 0 END) as verified,
            ROUND(SUM(CASE WHEN verified THEN 1 ELSE 0 END) * 100.0 / COUNT(*), 2) as success_rate
        FROM df
        GROUP BY exercise
        ORDER BY success_rate DESC
    """
    ).df()


def success_rate_by_model_and_exercise(df: pd.DataFrame | None = None) -> pd.DataFrame:
    """Compute success rate per model and exercise combination.

    Returns DataFrame with columns: model, exercise, total, verified, success_rate.
    """
    if df is None:
        df = load_proofs()

    return duckdb.sql(
        """
        SELECT
            model,
            exercise,
            COUNT(*) as total,
            SUM(CASE WHEN verified THEN 1 ELSE 0 END) as verified,
            ROUND(SUM(CASE WHEN verified THEN 1 ELSE 0 END) * 100.0 / COUNT(*), 2) as success_rate
        FROM df
        GROUP BY model, exercise
        ORDER BY model, success_rate DESC
    """
    ).df()
