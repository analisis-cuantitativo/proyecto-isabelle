from pathlib import Path

from pypdf import PdfReader


def load_text(pdf_path: str | Path, pages: list[int] | None = None) -> str:
    """Load and extract text from a PDF file.

    Args:
        pdf_path: Path to the PDF file.
        pages: Optional list of page indices (0-indexed) to extract.
            If None, extracts all pages.

    Returns:
        The extracted text content from the specified pages.
    """
    reader = PdfReader(pdf_path)
    if pages is None:
        text_parts = [page.extract_text() for page in reader.pages]
    else:
        text_parts = [reader.pages[i].extract_text() for i in pages]
    return "\n".join(text_parts)


def save_text(text: str, path: Path | str) -> None:
    """
    Esta función guarda el texto en un archivo en path
    especificado.
    """
    ...
