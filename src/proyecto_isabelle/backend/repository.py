from typing import Any

from proyecto_isabelle.backend.dto import ExerciseResponse
from proyecto_isabelle.sync.models import Source
from proyecto_isabelle.sync.repository import SupabaseRepository

_repo: "APIReviewRepository | None" = None


def get_repository() -> "APIReviewRepository":
    global _repo
    if _repo is None:
        _repo = APIReviewRepository()
    return _repo


class APIReviewRepository(SupabaseRepository):
    def _row_to_source(self, source_id: int) -> Source:
        resp = self.client.table("source").select("*").eq("id", source_id).execute()
        row = (resp.data or [{}])[0]

        author_ids_resp = (
            self.client.table("source_author")
            .select("author_id")
            .eq("source_id", source_id)
            .execute()
        )
        author_ids = [
            r["author_id"]
            for r in (author_ids_resp.data or [])
            if r.get("author_id") is not None
        ]
        authors: list[str] = []
        if author_ids:
            authors_resp = (
                self.client.table("author")
                .select("name")
                .in_("id", author_ids)
                .execute()
            )
            authors = sorted(
                [
                    r["name"]
                    for r in (authors_resp.data or [])
                    if r.get("name")
                ]
            )

        return Source(
            title=row.get("title") or "",
            authors=authors,
            section=row.get("section") or "",
            publication_year=row.get("publication_year") or 0,
            source_page=row.get("source_page") or "",
        )

    def _load_topics(self, exercise_id: int) -> list[str]:
        link_resp = (
            self.client.table("exercise_topic")
            .select("topic_id")
            .eq("exercise_id", exercise_id)
            .execute()
        )
        topic_ids = [
            r["topic_id"]
            for r in (link_resp.data or [])
            if r.get("topic_id") is not None
        ]
        if not topic_ids:
            return []
        topics_resp = (
            self.client.table("topic")
            .select("name")
            .in_("id", topic_ids)
            .execute()
        )
        return sorted(
            [r["name"] for r in (topics_resp.data or []) if r.get("name")]
        )

    def _load_requirements(self, exercise_id: int) -> list[str]:
        link_resp = (
            self.client.table("exercise_requirement")
            .select("requirement_id")
            .eq("exercise_id", exercise_id)
            .execute()
        )
        req_ids = [
            r["requirement_id"]
            for r in (link_resp.data or [])
            if r.get("requirement_id") is not None
        ]
        if not req_ids:
            return []
        reqs_resp = (
            self.client.table("requirement")
            .select("name")
            .in_("id", req_ids)
            .execute()
        )
        return sorted(
            [r["name"] for r in (reqs_resp.data or []) if r.get("name")]
        )

    def _row_to_exercise(self, row: dict) -> ExerciseResponse:
        source_id = row.get("source_id")
        source = Source(
            title="", authors=[], section="", publication_year=0, source_page=""
        )
        if source_id is not None:
            source = self._row_to_source(int(source_id))

        ex_id = row.get("id")
        topics: list[str] = []
        requirements: list[str] = []
        if ex_id is not None:
            topics = self._load_topics(int(ex_id))
            requirements = self._load_requirements(int(ex_id))

        return ExerciseResponse(
            id=row.get("id", 0),
            name=row.get("name", ""),
            source=source,
            topics=topics,
            requirements=requirements if requirements else None,
            is_verified=bool(row.get("is_verified", False)),
            msc_code=row.get("msc_code"),
            license=row.get("license"),
            proposed_thy_code=row.get("proposed_thy_code"),
            corrected_thy_code=row.get("corrected_thy_code"),
            statement=row.get("statement"),
            proof=row.get("proof"),
        )

    def list_exercises(
        self,
        *,
        limit: int = 50,
        after_id: int | None = None,
        is_verified: bool | None = None,
    ) -> tuple[list[ExerciseResponse], int | None]:
        q = self.client.table("exercise").select("*")
        if is_verified is not None:
            q = q.eq("is_verified", is_verified)
        if after_id is not None:
            q = q.gt("id", after_id)
        q = q.order("id", desc=False).limit(limit)

        resp = q.execute()
        rows = resp.data or []
        out = [self._row_to_exercise(row) for row in rows]

        next_after_id: int | None = None
        if rows:
            last_id = rows[-1].get("id")
            if isinstance(last_id, int):
                next_after_id = last_id
            elif last_id is not None:
                try:
                    next_after_id = int(last_id)
                except (TypeError, ValueError):
                    next_after_id = None

        return out, next_after_id

    def get_exercise_by_id(self, exercise_id: int) -> ExerciseResponse | None:
        resp = (
            self.client.table("exercise")
            .select("*")
            .eq("id", exercise_id)
            .execute()
        )
        if not resp.data:
            return None
        return self._row_to_exercise(resp.data[0])

    def get_exercise_by_name(self, name: str) -> ExerciseResponse | None:
        resp = (
            self.client.table("exercise")
            .select("*")
            .eq("name", name)
            .execute()
        )
        if not resp.data:
            return None
        return self._row_to_exercise(resp.data[0])

    def update_exercise(self, exercise_id: int, payload: dict[str, Any]) -> None:
        self.client.table("exercise").update(payload).eq("id", exercise_id).execute()
