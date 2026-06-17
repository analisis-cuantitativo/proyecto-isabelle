from proyecto_isabelle.backend.dto import IsabelleValidationResult

# TODO: temporal — reemplazar con DeepIsaHOL en el futuro


def validate_isabelle_code(code: str) -> IsabelleValidationResult:
    errors: list[str] = []
    warnings: list[str] = []

    if not code:
        errors.append("No se proporciono codigo Isabelle.")

    if code and "sorry" in code:
        warnings.append("El codigo contiene 'sorry': la prueba esta incompleta.")

    if code and "theory" not in code:
        errors.append("No se encontro la declaracion 'theory'.")

    if code and "end" not in code:
        warnings.append("Posible falta de cierre 'end' en la theory.")

    if code and "lemma" not in code and "theorem" not in code:
        warnings.append("No se encontro un lemma o teorema declarado.")

    is_valid = len(errors) == 0

    return IsabelleValidationResult(
        is_valid=is_valid, errors=errors, warnings=warnings
    )
