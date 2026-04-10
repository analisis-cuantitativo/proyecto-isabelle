import hashlib


def sanitize_model_name(model: str) -> str:
    """Convert model name to a valid directory name."""
    return model.replace("/", "_").replace(":", "_")


def generate_hash(content: str, timestamp: str) -> str:
    """Generate a short hash based on content and timestamp."""
    combined = f"{content}{timestamp}"
    return hashlib.sha256(combined.encode()).hexdigest()[:12]
