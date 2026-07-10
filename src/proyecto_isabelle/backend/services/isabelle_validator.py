from proyecto_isabelle.query import isabelle


def validate_isabelle_code(code: str) -> isabelle.IsabelleResponse:
    return isabelle.query_content(code)
