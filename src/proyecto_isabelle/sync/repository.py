import os
from dataclasses import dataclass
from enum import Enum
from uuid import uuid4

from supabase import create_client, Client
from dotenv import load_dotenv

from proyecto_isabelle.sync.models import Benchmark, Exercise, Source
from proyecto_isabelle.query.proof_agent import IsabelleCheck

load_dotenv()


class WriteStatus(str, Enum):
    CREATED = "created"
    UPDATED = "updated"
    UNCHANGED = "unchanged"


@dataclass(frozen=True, slots=True)
class WriteResult:
    status: WriteStatus
    exercise_id: int
    changed_fields: set[str]


class SupabaseRepository:
    def __init__(self):
        supabase_url: str = os.environ.get("SUPABASE_URL", "")
        supabase_key: str = os.environ.get("SUPABASE_KEY", "")
        supabase_email: str = os.environ.get("SUPABASE_EMAIL", "")
        supabase_password: str = os.environ.get("SUPABASE_PASSWORD", "")

        if (
            not supabase_url
            or not supabase_key
            or not supabase_email
            or not supabase_password
        ):
            raise ValueError(
                "Missing environment variables: SUPABASE_URL, SUPABASE_KEY,"
                " SUPABASE_EMAIL, and SUPABASE_PASSWORD in .env"
            )

        self.client: Client = create_client(supabase_url, supabase_key)
        self.client.auth.sign_in_with_password(
            {
                "email": supabase_email,
                "password": supabase_password,
            }
        )

    @staticmethod
    def _norm(value):
        """Cadena vacía y None son el mismo estado: 'no hay valor'."""
        return None if value == "" else value

    def _get_or_create_author(self, author_name: str) -> int:
        """Search for author by name."""
        resp = (
            self.client.table("author").select("id").eq("name", author_name).execute()
        )
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = (
            self.client.table("author").insert({"name": author_name}).execute()
        )
        return insert_resp.data[0]["id"]

    def _get_or_create_source(self, source_data: Source) -> int:
        """Search for source by ALL descriptive fields to ensure precision."""
        resp = (
            self.client.table("source")
            .select("id")
            .eq("title", source_data.title)
            .eq("section", source_data.section)
            .eq("publication_year", source_data.publication_year)
            .eq("source_page", source_data.source_page)
            .execute()
        )

        if resp.data:
            return resp.data[0]["id"]

        new_source = {
            "title": source_data.title,
            "section": source_data.section,
            "publication_year": source_data.publication_year,
            "source_page": source_data.source_page,
        }
        insert_resp = self.client.table("source").insert(new_source).execute()
        source_id = insert_resp.data[0]["id"]

        # Link authors
        for author_name in source_data.authors:
            author_id = self._get_or_create_author(author_name)
            self.client.table("source_author").insert(
                {"source_id": source_id, "author_id": author_id}
            ).execute()

        return source_id

    def _get_or_create_topic(self, topic_name: str) -> int:
        """Search for topic by name."""
        resp = self.client.table("topic").select("id").eq("name", topic_name).execute()
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = self.client.table("topic").insert({"name": topic_name}).execute()
        return insert_resp.data[0]["id"]

    def _get_or_create_requirement(self, req_name: str) -> int:
        """Search for requirement by name."""
        resp = (
            self.client.table("requirement").select("id").eq("name", req_name).execute()
        )
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = (
            self.client.table("requirement").insert({"name": req_name}).execute()
        )
        return insert_resp.data[0]["id"]

    def save_benchmark(
        self,
        exercise: Exercise,
        checks: list[IsabelleCheck],
        model_name: str,
        max_num_of_passes: int,
        tokens_consumed: int = 0,
        hit_retry_budget: bool = False,
    ) -> None:
        """Persist one proof-agent run as one `benchmark` row per pass.

        All rows share a fresh ``run_id``; the row with the highest
        ``pass_number`` is the run's final answer (by convention, callers
        should make that the independently-reverified attempt, not just the
        model's last self-reported check). Works the same whether the run
        finished normally or was cut short by ``ProofBudgetExceeded`` — pass
        that exception's ``.checks`` and ``hit_retry_budget=True``.
        """
        if exercise.id is None:
            raise ValueError("Exercise needs an id to be turned into Benchmark rows.")
        if not checks:
            raise ValueError(
                "No checks to persist — the run never called check_in_isabelle."
            )

        run_id = uuid4()
        was_given_correct = (
            exercise.corrected_thy_code is not None
            and exercise.statement == exercise.corrected_thy_code
        )

        rows = [
            Benchmark(
                run_id=run_id,
                pass_number=i,
                exercise_id=exercise.id,
                model_name=model_name,
                was_given_the_correct_thy_statement=was_given_correct,
                thy_content=check.thy_content,
                verified=check.verified,
                errors=check.errors,
                max_num_of_passes=max_num_of_passes,
                hit_retry_budget=hit_retry_budget,
                tokens_consumed=tokens_consumed,
            )
            for i, check in enumerate(checks, start=1)
        ]

        self.client.table("benchmark").insert(
            [row.model_dump(mode="json") for row in rows]
        ).execute()

    def _sync_link_table(
        self, table: str, fk_column: str, exercise_id: int, wanted_ids: list[int]
    ) -> bool:
        """Diff-based sync of a join table. Returns True if anything changed."""
        rows = (
            self.client.table(table)
            .select(fk_column)
            .eq("exercise_id", exercise_id)
            .execute()
        )
        current_ids = {row[fk_column] for row in rows.data}
        wanted = set(wanted_ids)

        if current_ids == wanted:
            return False

        to_delete = current_ids - wanted
        if to_delete:
            self.client.table(table).delete().eq("exercise_id", exercise_id).in_(
                fk_column, list(to_delete)
            ).execute()

        to_insert = wanted - current_ids
        if to_insert:
            self.client.table(table).insert(
                [{"exercise_id": exercise_id, fk_column: fk_id} for fk_id in to_insert]
            ).execute()

        return True

    def read(self, exercise_name: str) -> dict:
        """Reads an exercise by name."""
        response = (
            self.client.table("exercise")
            .select("*")
            .eq("name", exercise_name)
            .execute()
        )
        if not response.data:
            raise ValueError(f"Exercise not found: {exercise_name}")
        return response.data[0]

    def read_as_exercise(self, exercise_name: str) -> Exercise:
        response = (
            self.client.table("exercise_full")
            .select("*")
            .eq("name", exercise_name)
            .execute()
        )
        if not response.data:
            raise ValueError(f"Exercise not found: {exercise_name}")
        return Exercise.model_validate(response.data[0])

    def get_missing_exercises_by_model(self, model_name: str) -> list[Exercise]:
        """
        Returns a list of exercises that have not been iterated by the given model.
        """
        benchmark_response = (
            self.client.table("benchmark")
            .select("exercise_id")
            .eq("model_name", model_name)
            .execute()
        )

        iterated_ids = [row["exercise_id"] for row in benchmark_response.data]

        query = self.client.table("exercise_full").select("*")

        if iterated_ids:
            query = query.not_.in_("id", iterated_ids)

        response = query.execute()

        return [Exercise.model_validate(row) for row in response.data]

    def write(self, exercise: Exercise) -> WriteResult:
        """
        1. Resolve unique source (using exhaustive field matching).
        2. Identify exercise by composite key: Name + SourceID.
        3. Insert, or update ONLY the provided fields that actually differ.
        4. Synchronize M:N relationships (Topics and Requirements).

        Fields absent from the input are never touched. Fields explicitly set
        to None are written as NULL.
        """
        # Resolve source using exhaustive validation
        source_id = self._get_or_create_source(exercise.source)

        # Check if exercise exists within this specific source
        resp = (
            self.client.table("exercise")
            .select("*")
            .eq("name", exercise.name)
            .eq("source_id", source_id)
            .execute()
        )

        # Which keys the input actually carried (absent != None)
        provided = exercise.model_dump(exclude_unset=True)

        # map the Exercise
        db_payload = {
            "name": exercise.name,
            "source_id": source_id,
            "proposed_thy_code": exercise.proposed_thy_code,
            "license": exercise.license,
            "msc_code": exercise.msc_code,
            "is_verified": exercise.is_verified,
            "corrected_thy_code": exercise.corrected_thy_code,
            "statement": exercise.statement,
            "proof": exercise.proof,
        }

        # filter out fields
        db_payload = {
            key: self._norm(value)
            for key, value in db_payload.items()
            if key in provided or key in ("name", "source_id")
        }

        # Upsert
        if not resp.data:
            ex_resp = self.client.table("exercise").insert(db_payload).execute()
            exercise_id = ex_resp.data[0]["id"]
            created = True
        else:
            current = resp.data[0]
            exercise_id = current["id"]
            created = False

            # Identity is the lookup key: never part of the diff
            db_payload.pop("name")
            db_payload.pop("source_id")

            db_payload = {
                key: value
                for key, value in db_payload.items()
                if self._norm(current.get(key)) != value
            }

            # El enunciado cambió: el trabajo previo ya no le corresponde
            if "statement" in db_payload:
                if "proposed_thy_code" not in provided:
                    db_payload["proposed_thy_code"] = None
                if "corrected_thy_code" not in provided:
                    db_payload["corrected_thy_code"] = None
                if "is_verified" not in provided:
                    db_payload["is_verified"] = False

            if db_payload:
                self.client.table("exercise").update(db_payload).eq(
                    "id", exercise_id
                ).execute()

        # M:N: only the relations the input mentioned
        changed_links: set[str] = set()

        if "topics" in provided:
            topic_ids = [
                self._get_or_create_topic(topic_name)
                for topic_name in exercise.topics or []
            ]
            if self._sync_link_table(
                "exercise_topic", "topic_id", exercise_id, topic_ids
            ):
                changed_links.add("topics")

        if "requirements" in provided:
            req_ids = [
                self._get_or_create_requirement(req_name)
                for req_name in exercise.requirements or []
            ]
            if self._sync_link_table(
                "exercise_requirement", "requirement_id", exercise_id, req_ids
            ):
                changed_links.add("requirements")

        # Report
        if created:
            return WriteResult(WriteStatus.CREATED, exercise_id, set(db_payload))

        if not db_payload and not changed_links:
            return WriteResult(WriteStatus.UNCHANGED, exercise_id, set())

        return WriteResult(
            WriteStatus.UPDATED, exercise_id, set(db_payload) | changed_links
        )

    def read_with_empty_proposed_thy(self) -> list[Exercise]:
        # Un solo request usando .or_()
        response = (
            self.client.table("exercise_full")
            .select("*")
            .or_("proposed_thy_code.is.null,proposed_thy_code.eq.")
            .execute()
        )

        return [Exercise.model_validate(ex) for ex in response.data]
