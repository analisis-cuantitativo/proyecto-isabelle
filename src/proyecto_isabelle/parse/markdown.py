from pathlib import Path


def load_text(path: Path | str) -> str:
    if not isinstance(path, Path):
        path = Path(path)

    with path.open("r") as fp:
        res = fp.read()

    return res


def save_text(text: str, path: str | Path) -> None:
    """
    Esta función guarda el texto en un archivo en path
    especificado.
    """
    with open(path, "w") as archivo:
        archivo.write(text)
