from pydantic import BaseModel


class Source(BaseModel):
    title: str
    authors: list[str]
    section: str
    publication_year: int
    source_page: str


class Exercise(BaseModel):
    """Dedicated object for exercises using Pydantic, as requested in the issue"""

    name: str
    source: Source
    topics: list[str]
    requirements: list[str] | None
    is_verified: bool
    msc_code: str | None = None
    license: str | None = None
    proposed_thy_code: str | None = None
    corrected_thy_code: str | None = None
    statement: str | None = None
    proof: str | None = None
