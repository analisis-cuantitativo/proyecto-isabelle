def sanitize_model_name(model: str) -> str:
    """Convert model name to a valid directory name."""
    return model.replace("/", "_").replace(":", "_")
