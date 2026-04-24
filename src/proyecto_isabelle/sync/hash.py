"""MD5 hash utility for file comparison."""

import base64
import hashlib
from pathlib import Path


def compute_md5(file_path: Path) -> str:
    """Compute MD5 hash of a file, returning base64-encoded string.

    GCS stores MD5 hashes as base64-encoded strings, so we match that format
    for easy comparison.

    Args:
        file_path: Path to the file to hash.

    Returns:
        Base64-encoded MD5 hash string.
    """
    md5_hash = hashlib.md5()
    with open(file_path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            md5_hash.update(chunk)
    return base64.b64encode(md5_hash.digest()).decode("utf-8")
