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
    
    return fp.read_text(encoding="utf-8") #formato de texto utf-8 para evitar problemas con caracteres especiales
