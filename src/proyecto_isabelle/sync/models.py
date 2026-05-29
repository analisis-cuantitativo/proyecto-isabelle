from pydantic import BaseModel
from typing import List, Optional


class Source(BaseModel):
    title: str
    authors: List[str]
    section: str
    publication_year: int
    source_page: str


class Exercise(BaseModel):
    """Dedicated object for exercises using Pydantic, as requested in the issue"""

    name: str
    source: Source
    topics: List[str]
    requirements: List[str]
    is_verified: bool
    msc_code: Optional[str] = None
    license: Optional[str] = None
    proposed_thy_code: Optional[str] = None
    corrected_thy_code: Optional[str] = None
    statement: Optional[str] = None
    proof_tex: Optional[str] = None
