from pathlib import Path

from pypdf import PdfReader


def load_text(pdf_path: str | Path) -> str:
    """Load and extract text from a PDF file.

    Args:
        pdf_path: Path to the PDF file.

    Returns:
        The extracted text content from all pages.
    """
    reader = PdfReader(pdf_path)
    text_parts = [page.extract_text() for page in reader.pages]
    return "\n".join(text_parts)
