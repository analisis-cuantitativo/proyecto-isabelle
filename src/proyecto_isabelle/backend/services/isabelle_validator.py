from proyecto_isabelle.backend.dto import IsabelleValidationResult

# TODO: temporal — reemplazar con DeepIsaHOL en el futuro


def validate_isabelle_code(code: str) -> IsabelleValidationResult:
    errors: list[str] = []
    warnings: list[str] = []

    if not code:
        errors.append("No se proporcionó código Isabelle.")

    if code and "sorry" in code:
        warnings.append("El código contiene 'sorry': la prueba está incompleta.")

    if code and "theory" not in code:
        errors.append("No se encontró la declaración 'theory'.")

    if code and "end" not in code:
        warnings.append("Posible falta de cierre 'end' en la teoría.")

    if code and "lemma" not in code and "theorem" not in code:
        warnings.append("No se encontró un lemma o teorema declarado.")

    is_valid = len(errors) == 0

    return IsabelleValidationResult(is_valid=is_valid, errors=errors, warnings=warnings)
