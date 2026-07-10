import os
from supabase import create_client, Client
from dotenv import load_dotenv

from proyecto_isabelle.sync.models import Exercise, Source

load_dotenv()


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

    def write(self, exercise: Exercise) -> None:
        """
        1. Resolve unique source (using exhaustive field matching).
        2. Identify exercise by composite key: Name + SourceID.
        3. Perform Upsert (Update or Insert).
        4. Synchronize M:N relationships (Topics and Requirements).
        """
        # Resolve source using exhaustive validation
        source_id = self._get_or_create_source(exercise.source)

        # Check if exercise exists within this specific source
        resp = (
            self.client.table("exercise")
            .select("id")
            .eq("name", exercise.name)
            .eq("source_id", source_id)
            .execute()
        )

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

        # Update or Insert
        if resp.data:
            exercise_id = resp.data[0]["id"]
            self.client.table("exercise").update(db_payload).eq(
                "id", exercise_id
            ).execute()
        else:
            ex_resp = self.client.table("exercise").insert(db_payload).execute()
            exercise_id = ex_resp.data[0]["id"]

        # Clear old links, add new ones
        self.client.table("exercise_topic").delete().eq(
            "exercise_id", exercise_id
        ).execute()
        self.client.table("exercise_requirement").delete().eq(
            "exercise_id", exercise_id
        ).execute()

        for topic_name in exercise.topics:
            topic_id = self._get_or_create_topic(topic_name)
            self.client.table("exercise_topic").insert(
                {"exercise_id": exercise_id, "topic_id": topic_id}
            ).execute()

        for req_name in exercise.requirements or []:
            req_id = self._get_or_create_requirement(req_name)
            self.client.table("exercise_requirement").insert(
                {"exercise_id": exercise_id, "requirement_id": req_id}
            ).execute()

    def read_with_empty_proposed_thy(self) -> list[Exercise]:
        res_null = (
            self.client.table("exercise_full")
            .select("*")
            .filter("proposed_thy_code", "is", "null")
            .execute()
        )

        res_empty = (
            self.client.table("exercise_full")
            .select("*")
            .eq("proposed_thy_code", "")
            .execute()
        )

        return [
            Exercise.model_validate(exercise)
            for exercise in res_null.data + res_empty.data
        ]
