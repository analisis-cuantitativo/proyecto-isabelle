from proyecto_isabelle.query import isabelle


def validate_isabelle_code(code: str) -> isabelle.IsabelleResponse:
    # Web-app validation uses the fast REPL path: skeletons are checked against
    # `Main` for parse/type errors and the reviewer wants a snappy response. The
    # benchmark agent uses `mode="build"` instead.
    return isabelle.query_content(code, mode="verify")
