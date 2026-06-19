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
                [r["name"] for r in (authors_resp.data or []) if r.get("name")]
            )

        return Source(
            title=row.get("title") or "",
            authors=authors,
            section=row.get("section") or "",
            publication_year=row.get("publication_year") or 0,
            source_page=row.get("source_page") or "",
        )

    def _batch_get_sources(self, source_ids: set[int]) -> dict[int, Source]:
        if not source_ids:
            return {}
        ids_list = list(source_ids)
        sources_resp = (
            self.client.table("source").select("*").in_("id", ids_list).execute()
        )
        sources_rows = sources_resp.data or []
        sa_resp = (
            self.client.table("source_author")
            .select("source_id, author_id")
            .in_("source_id", ids_list)
            .execute()
        )
        sa_rows = sa_resp.data or []
        author_ids = {r["author_id"] for r in sa_rows if r.get("author_id") is not None}
        authors_map: dict[int, str] = {}
        if author_ids:
            authors_resp = (
                self.client.table("author")
                .select("id, name")
                .in_("id", list(author_ids))
                .execute()
            )
            for r in authors_resp.data or []:
                if r.get("id") is not None and r.get("name"):
                    authors_map[r["id"]] = r["name"]
        source_author_map: dict[int, list[int]] = {}
        for r in sa_rows:
            sid = r.get("source_id")
            aid = r.get("author_id")
            if sid is not None and aid is not None:
                source_author_map.setdefault(sid, []).append(aid)
        result: dict[int, Source] = {}
        for row in sources_rows:
            sid = row.get("id")
            if sid is None:
                continue
            author_names = sorted(
                authors_map[aid]
                for aid in source_author_map.get(sid, [])
                if aid in authors_map
            )
            result[sid] = Source(
                title=row.get("title") or "",
                authors=author_names,
                section=row.get("section") or "",
                publication_year=row.get("publication_year") or 0,
                source_page=row.get("source_page") or "",
            )
        return result

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
            self.client.table("topic").select("name").in_("id", topic_ids).execute()
        )
        return sorted([r["name"] for r in (topics_resp.data or []) if r.get("name")])

    def _batch_get_topics(self, exercise_ids: set[int]) -> dict[int, list[str]]:
        if not exercise_ids:
            return {}
        ids_list = list(exercise_ids)
        et_resp = (
            self.client.table("exercise_topic")
            .select("exercise_id, topic_id")
            .in_("exercise_id", ids_list)
            .execute()
        )
        et_rows = et_resp.data or []
        topic_ids = {r["topic_id"] for r in et_rows if r.get("topic_id") is not None}
        topics_map: dict[int, str] = {}
        if topic_ids:
            topics_resp = (
                self.client.table("topic")
                .select("id, name")
                .in_("id", list(topic_ids))
                .execute()
            )
            for r in topics_resp.data or []:
                if r.get("id") is not None and r.get("name"):
                    topics_map[r["id"]] = r["name"]
        result: dict[int, list[str]] = {}
        for r in et_rows:
            eid = r.get("exercise_id")
            tid = r.get("topic_id")
            if eid is not None and tid is not None and tid in topics_map:
                result.setdefault(eid, []).append(topics_map[tid])
        for names in result.values():
            names.sort()
        return result

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
            self.client.table("requirement").select("name").in_("id", req_ids).execute()
        )
        return sorted([r["name"] for r in (reqs_resp.data or []) if r.get("name")])

    def _batch_get_requirements(self, exercise_ids: set[int]) -> dict[int, list[str]]:
        if not exercise_ids:
            return {}
        ids_list = list(exercise_ids)
        er_resp = (
            self.client.table("exercise_requirement")
            .select("exercise_id, requirement_id")
            .in_("exercise_id", ids_list)
            .execute()
        )
        er_rows = er_resp.data or []
        req_ids = {
            r["requirement_id"] for r in er_rows if r.get("requirement_id") is not None
        }
        reqs_map: dict[int, str] = {}
        if req_ids:
            reqs_resp = (
                self.client.table("requirement")
                .select("id, name")
                .in_("id", list(req_ids))
                .execute()
            )
            for r in reqs_resp.data or []:
                if r.get("id") is not None and r.get("name"):
                    reqs_map[r["id"]] = r["name"]
        result: dict[int, list[str]] = {}
        for r in er_rows:
            eid = r.get("exercise_id")
            rid = r.get("requirement_id")
            if eid is not None and rid is not None and rid in reqs_map:
                result.setdefault(eid, []).append(reqs_map[rid])
        for names in result.values():
            names.sort()
        return result

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

        if not rows:
            return [], None

        source_ids = {
            row.get("source_id") for row in rows if row.get("source_id") is not None
        }
        exercise_ids = {row.get("id") for row in rows if row.get("id") is not None}

        sources_map = self._batch_get_sources(source_ids)
        topics_map = self._batch_get_topics(exercise_ids)
        requirements_map = self._batch_get_requirements(exercise_ids)

        default_source = Source(
            title="", authors=[], section="", publication_year=0, source_page=""
        )
        out: list[ExerciseResponse] = []
        for row in rows:
            source_id = row.get("source_id")
            if source_id is not None and source_id in sources_map:
                source = sources_map[source_id]
            else:
                source = default_source

            ex_id = row.get("id")
            topics = topics_map.get(ex_id, []) if ex_id is not None else []
            requirements = requirements_map.get(ex_id) if ex_id is not None else None

            out.append(
                ExerciseResponse(
                    id=row.get("id", 0),
                    name=row.get("name", ""),
                    source=source,
                    topics=topics,
                    requirements=requirements,
                    is_verified=bool(row.get("is_verified", False)),
                    msc_code=row.get("msc_code"),
                    license=row.get("license"),
                    proposed_thy_code=row.get("proposed_thy_code"),
                    corrected_thy_code=row.get("corrected_thy_code"),
                    statement=row.get("statement"),
                    proof=row.get("proof"),
                )
            )

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
        resp = self.client.table("exercise").select("*").eq("id", exercise_id).execute()
        if not resp.data:
            return None
        return self._row_to_exercise(resp.data[0])

    def get_exercise_by_name(self, name: str) -> ExerciseResponse | None:
        resp = self.client.table("exercise").select("*").eq("name", name).execute()
        if not resp.data:
            return None
        return self._row_to_exercise(resp.data[0])

    def update_exercise(self, exercise_id: int, payload: dict[str, Any]) -> None:
        self.client.table("exercise").update(payload).eq("id", exercise_id).execute()
