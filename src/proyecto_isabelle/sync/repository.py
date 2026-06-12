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

    # ASSISTANT FUNCTIONS FOR MANAGING RELATIONSHIPS (FOREIGN KEYS)

    def _get_or_create_author(self, author_name: str) -> int:
        """Searches for an author; creates one if it doesn't exist and returns its ID."""
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
        """
        Searches for a source using all descriptive fields to ensure
        uniqueness across different book sections or pages.
        """
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

        # Create source if it doesn't exist
        new_source = {
            "title": source_data.title,
            "section": source_data.section,
            "publication_year": source_data.publication_year,
            "source_page": source_data.source_page,
        }
        insert_resp = self.client.table("source").insert(new_source).execute()
        source_id = insert_resp.data[0]["id"]

        # Link authors to the new source
        for author_name in source_data.authors:
            author_id = self._get_or_create_author(author_name)
            self.client.table("source_author").insert(
                {"source_id": source_id, "author_id": author_id}
            ).execute()

        return source_id

    def _get_or_create_topic(self, topic_name: str) -> int:
        """Searches for a topic; creates one if missing and returns its ID."""
        resp = self.client.table("topic").select("id").eq("name", topic_name).execute()
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = self.client.table("topic").insert({"name": topic_name}).execute()
        return insert_resp.data[0]["id"]

    def _get_or_create_requirement(self, req_name: str) -> int:
        """Searches for a requirement; creates one if missing and returns its ID."""
        resp = (
            self.client.table("requirement").select("id").eq("name", req_name).execute()
        )
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = (
            self.client.table("requirement").insert({"name": req_name}).execute()
        )
        return insert_resp.data[0]["id"]

    # MAIN METHODS
    def read(self, exercise_name: str) -> dict:
        """Reads an exercise by its name."""
        response = (
            self.client.table("exercise")
            .select("*")
            .eq("name", exercise_name)
            .execute()
        )
        if not response.data:
            raise ValueError(f"Exercise not found: {exercise_name}")
        return response.data[0]

    def write(self, exercise: Exercise) -> None:
        """
        Intelligent Upsert:
        1. Identifies unique source.
        2. Searches exercise by 'name' + 'source_id' (Composite Identity).
        3. Updates existing record or creates a new one.
        4. Cleans and refreshes relationships (topics/requirements).
        """
        # 1. Resolve source ID based on exhaustive descriptive fields
        source_id = self._get_or_create_source(exercise.source)

        # 2. Check for existence using composite identity
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

        # 3. Perform update or insert
        if resp.data:
            exercise_id = resp.data[0]["id"]
            self.client.table("exercise").update(db_payload).eq(
                "id", exercise_id
            ).execute()
        else:
            ex_resp = self.client.table("exercise").insert(db_payload).execute()
            exercise_id = ex_resp.data[0]["id"]

        # 4. Refresh N:M relationships (Topics and Requirements)
        # Remove existing links before inserting current state
        self.client.table("exercise_topic").delete().eq(
            "exercise_id", exercise_id
        ).execute()
        self.client.table("exercise_requirement").delete().eq(
            "exercise_id", exercise_id
        ).execute()

        # Re-link current topics
        for topic_name in exercise.topics:
            topic_id = self._get_or_create_topic(topic_name)
            self.client.table("exercise_topic").insert(
                {"exercise_id": exercise_id, "topic_id": topic_id}
            ).execute()

        # Re-link current requirements
        for req_name in exercise.requirements or []:
            req_id = self._get_or_create_requirement(req_name)
            self.client.table("exercise_requirement").insert(
                {"exercise_id": exercise_id, "requirement_id": req_id}
            ).execute()
