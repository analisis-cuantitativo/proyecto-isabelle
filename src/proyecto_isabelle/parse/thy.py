from pathlib import Path


def load_text(path: str | Path) -> str:
    """
    Carga un archivo .thy en el path especificado.

    recibimos la dirección
    validamos que exista y que sea un archivo
    si está bien, se lee el contenido del archivo y se devuelve como una cadena de texto
    """
    fp = Path(path)

    if not fp.is_file():
        raise FileNotFoundError(f"El archivo {path} no existe.")

    return fp.read_text(
        encoding="utf-8"
    )  # formato de texto utf-8 para evitar problemas con caracteres especiales


def save_text(text: str, path: str | Path) -> None:
    """
    Esta función guarda el texto en un archivo en path
    especificado.
    """

    # Se crea el archivo en la ruta correspondiente si no existe y se escribe en el"
    with open(path, "w", encoding="utf-8") as archivo:
        archivo.write(text)
