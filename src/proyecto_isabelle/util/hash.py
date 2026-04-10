import hashlib


def generate_hash(content: str, timestamp: str) -> str:
    """Generate a short hash based on content and timestamp."""
    combined = f"{content}{timestamp}"
    return hashlib.sha256(combined.encode()).hexdigest()[:12]
