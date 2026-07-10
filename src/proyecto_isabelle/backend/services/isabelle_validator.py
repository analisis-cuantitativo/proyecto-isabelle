from proyecto_isabelle.backend.dto import IsabelleValidationResult

from proyecto_isabelle.query import isabelle


def validate_isabelle_code(code: str) -> IsabelleValidationResult:
    res = isabelle.query_content(code)
    return IsabelleValidationResult(
        is_valid=res.verified, errors=res.errors, warnings=[]
    )
