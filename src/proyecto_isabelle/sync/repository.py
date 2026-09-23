import os
from dataclasses import dataclass
from enum import Enum
from uuid import UUID

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

    def save_benchmark_pass(
        self,
        exercise: Exercise,
        check: IsabelleCheck,
        model_name: str,
        max_num_of_passes: int,
        run_id: UUID,
        pass_number: int,
        version: int,
        agent_revision: str,
    ) -> None:
        """Persist one `benchmark` row for a single pass, immediately.

        Callers insert one row per real ``check_in_isabelle`` call — plus one
        more for the final, independently-reverified attempt — as each
        happens, rather than batching a whole run's rows into one insert at
        the end. That way a run's progress survives a crash partway through
        (including one that isn't caught anywhere), instead of an
        end-of-run-only write losing everything.

        The row with the highest ``pass_number`` for a ``run_id`` is that
        run's final answer (by convention, callers should make that the
        independently-reverified attempt, not just the model's last
        self-reported check). ``hit_retry_budget`` isn't known at insert
        time — it starts ``False`` here and gets patched via
        ``mark_run_hit_retry_budget`` if the run actually aborts.

        ``run_id`` and ``pass_number`` are the caller's responsibility (unlike
        the old batch ``save_benchmark``, this can't derive ``pass_number``
        from a list position) — callers that also keep a local run log
        (``query/run_log.py``) should reuse the same ``run_id`` there, so the
        Supabase rows and the local log file refer to the same run.

        ``version`` and ``agent_revision`` are likewise the caller's to supply
        (from ``util.BENCHMARK_VERSION`` and
        ``util.current_agent_revision()``), and must stay fixed for a whole
        campaign — they're what makes rows from different campaigns separable
        and each campaign's conditions auditable after the fact.
        """
        if exercise.id is None:
            raise ValueError("Exercise needs an id to be turned into a Benchmark row.")

        was_given_correct = (
            exercise.corrected_thy_code is not None
            and exercise.statement == exercise.corrected_thy_code
        )

        row = Benchmark(
            version=version,
            agent_revision=agent_revision,
            run_id=run_id,
            pass_number=pass_number,
            exercise_id=exercise.id,
            model_name=model_name,
            was_given_the_correct_thy_statement=was_given_correct,
            thy_content=check.thy_content,
            verified=check.verified,
            errors=check.errors,
            max_num_of_passes=max_num_of_passes,
            tokens_consumed=check.tokens_consumed,
        )

        self.client.table("benchmark").insert(row.model_dump(mode="json")).execute()

    def mark_run_hit_retry_budget(self, run_id: UUID) -> None:
        """Flag every already-inserted pass of ``run_id`` as having hit the
        retry budget, once ``ProofBudgetExceeded`` confirms that happened.

        Patches rows written eagerly by ``save_benchmark_pass`` during the
        run, before this was known.
        """
        self.client.table("benchmark").update({"hit_retry_budget": True}).eq(
            "run_id", str(run_id)
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

    def get_missing_exercises_by_model(
        self, model_name: str, version: int
    ) -> list[Exercise]:
        """Exercises `model_name` hasn't attempted yet *in campaign `version`*,
        with exercises no model has attempted in that campaign sorted first.

        `run_all` truncates this list with `--limit`, so the ordering matters:
        without it, a short/interrupted run would keep re-covering exercises
        other models already have data for instead of growing the benchmark's
        overall exercise coverage. Exercises already attempted by `model_name`
        are excluded outright (that's the "missing" part); among the rest,
        never-attempted-by-anyone exercises come before ones other models
        have already tried, and each of those two groups is alphabetical by
        exercise name.

        `version` scopes all of that to one campaign, and isn't optional: a
        campaign-2 run that saw campaign-1 rows would consider every exercise
        already covered and return nothing at all, silently doing no work
        instead of re-running the grid it was invoked to re-run.

        Paginated via ``.range()`` for the same reason `list_benchmark_rows`
        is: PostgREST caps an unpaginated response at `db.max_rows` (1000),
        and a truncated read here makes already-attempted exercises look
        never-attempted, so a resumed run re-proves them — burning tokens and
        writing duplicate runs for exercises that were already covered.
        """
        page_size = 1000
        benchmark_rows: list[dict] = []
        start = 0
        while True:
            response = (
                self.client.table("benchmark")
                .select("exercise_id, model_name")
                .eq("version", version)
                .range(start, start + page_size - 1)
                .execute()
            )
            benchmark_rows.extend(response.data)
            if len(response.data) < page_size:
                break
            start += page_size

        attempted_by_model: set[int] = set()
        attempted_by_any: set[int] = set()
        for row in benchmark_rows:
            attempted_by_any.add(row["exercise_id"])
            if row["model_name"] == model_name:
                attempted_by_model.add(row["exercise_id"])

        query = self.client.table("exercise_full").select("*")

        if attempted_by_model:
            query = query.not_.in_("id", list(attempted_by_model))

        response = query.execute()

        exercises = [Exercise.model_validate(row) for row in response.data]
        exercises.sort(key=lambda e: (e.id in attempted_by_any, e.name))
        return exercises

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

    def list_benchmarkable_exercises(self) -> list[dict]:
        """``{id, name}`` for every exercise with a statement, i.e. one the
        proof agent could actually be run against. Used as the denominator
        for dashboard coverage stats — an exercise with no statement can
        never produce a `benchmark` row (`query_content` raises on it), so
        it shouldn't count against an agent's coverage.
        """
        response = (
            self.client.table("exercise")
            .select("id, name")
            .not_.is_("statement", "null")
            .execute()
        )
        return response.data

    def list_benchmark_rows(self, version: int | None = None) -> list[dict]:
        """Raw ``{exercise_id, model_name, run_id, pass_number, verified,
        hit_retry_budget, version}`` for every pass ever recorded, across all
        models — or just campaign ``version``'s, when given.

        ``version=None`` means every campaign, which is almost never what an
        aggregate stat wants: campaigns ran under different agent revisions,
        so pooling them averages incomparable results. Callers that report a
        rate should pass an explicit ``version``; the column is selected
        either way so a caller that does pool can at least see it happening.

        Dicts rather than ``Benchmark`` instances, and only these columns —
        the dashboard's aggregate stats page groups/counts over them and has
        no use for the (potentially large) ``thy_content``/``errors`` fields.

        Paginated via ``.range()``: PostgREST caps a single unpaginated
        response at its ``db.max_rows`` setting (1000 here), so a single
        ``.execute()`` silently truncated this once the table passed that
        size — the dashboard then lost visibility into whichever
        exercise/model attempts happened to land past the cutoff, making
        recently-attempted exercises look never-attempted.
        """
        page_size = 1000
        rows: list[dict] = []
        start = 0
        while True:
            query = self.client.table("benchmark").select(
                "exercise_id, model_name, run_id, pass_number, verified, "
                "hit_retry_budget, version"
            )
            if version is not None:
                query = query.eq("version", version)
            response = query.range(start, start + page_size - 1).execute()
            rows.extend(response.data)
            if len(response.data) < page_size:
                break
            start += page_size
        return rows

    def list_campaign_rows(self) -> list[dict]:
        """``{version, agent_revision, model_name, run_id, exercise_id,
        created_at}`` for every pass ever recorded, across every campaign.

        Deliberately unfiltered: this is what tells a caller *which*
        campaigns exist and what conditions each one ran under (how many
        runs, which models, which agent revisions, when) — the questions you
        ask before picking a version to scope everything else to. The
        dashboard renders it as a campaign picker + summary; the aggregation
        lives there rather than here, like the other `list_*` readers.

        Six narrow columns on purpose: a campaign summary needs identity and
        counts, not `thy_content`/`errors`, and this one read is never scoped
        down by a filter.

        Paginated via ``.range()`` for the same reason as
        `list_benchmark_rows` (PostgREST's 1000-row cap per response) —
        truncation here would make a real campaign look smaller than it is,
        or hide its second agent revision, which is exactly the thing the
        summary exists to expose.
        """
        page_size = 1000
        rows: list[dict] = []
        start = 0
        while True:
            response = (
                self.client.table("benchmark")
                .select(
                    "version, agent_revision, model_name, run_id, exercise_id, "
                    "created_at"
                )
                .range(start, start + page_size - 1)
                .execute()
            )
            rows.extend(response.data)
            if len(response.data) < page_size:
                break
            start += page_size
        return rows

    def list_full_benchmark_rows(self, version: int | None = None) -> list[dict]:
        """Every `benchmark` column except `thy_content`, for every pass ever
        recorded, across all models — or just campaign ``version``'s, when
        given (see `list_benchmark_rows` on why pooling campaigns misleads).

        Unlike `list_benchmark_rows` (used by the dashboard's lean coverage
        stats), this keeps `errors` and `tokens_consumed` — the columns the
        offline analysis package (`proyecto_isabelle.analysis`) needs for
        token/error-pattern breakdowns. `thy_content` is still dropped: it's
        large and unused by any aggregate stat.

        Paginated the same way as `list_benchmark_rows`, for the same reason
        (PostgREST's default 1000-row cap per response).
        """
        page_size = 1000
        rows: list[dict] = []
        start = 0
        while True:
            query = self.client.table("benchmark").select(
                "id, run_id, pass_number, exercise_id, model_name, "
                "was_given_the_correct_thy_statement, verified, errors, "
                "max_num_of_passes, hit_retry_budget, tokens_consumed, "
                "created_at, version, agent_revision"
            )
            if version is not None:
                query = query.eq("version", version)
            response = query.range(start, start + page_size - 1).execute()
            rows.extend(response.data)
            if len(response.data) < page_size:
                break
            start += page_size
        return rows

    def list_all_exercises(self) -> list[Exercise]:
        """Every exercise with a statement (see `list_benchmarkable_exercises`
        for why that's the right filter), as full `Exercise` objects — topics,
        `msc_code`, and source included — for the offline analysis package.

        Paginated the same way as `list_full_benchmark_rows`.
        """
        page_size = 1000
        rows: list[dict] = []
        start = 0
        while True:
            response = (
                self.client.table("exercise_full")
                .select("*")
                .not_.is_("statement", "null")
                .range(start, start + page_size - 1)
                .execute()
            )
            rows.extend(response.data)
            if len(response.data) < page_size:
                break
            start += page_size
        return [Exercise.model_validate(row) for row in rows]

    def read_with_empty_proposed_thy(self) -> list[Exercise]:
        # Un solo request usando .or_()
        response = (
            self.client.table("exercise_full")
            .select("*")
            .or_("proposed_thy_code.is.null,proposed_thy_code.eq.")
            .execute()
        )

        return [Exercise.model_validate(ex) for ex in response.data]
