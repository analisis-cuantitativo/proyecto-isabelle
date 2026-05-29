import os
from supabase import create_client, Client
from dotenv import load_dotenv

from proyecto_isabelle.sync.models import Exercise, Source

load_dotenv()


class SupabaseRepository:
    def __init__(self):
        supabase_url: str = os.environ.get("SUPABASE_URL", "")
        supabase_key: str = os.environ.get("SUPABASE_KEY", "")

        if not supabase_url or not supabase_key:
            raise ValueError(
                "Faltan las variables de entorno SUPABASE_URL y SUPABASE_KEY en el .env"
            )

        self.client: Client = create_client(supabase_url, supabase_key)

    # ASSISTANT FUNCTIONS FOR MANAGING RELATIONSHIPS (FOREIGN KEYS)

    def _get_or_create_author(self, author_name: str) -> int:
        """It searches for an author. If it doesn't exist, it creates it and returns its ID."""
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
        """It searches for a source. If it doesn't exist, it creates it along with its authors and returns its ID."""
        # We search by title (assuming it is unique)
        resp = (
            self.client.table("source")
            .select("id")
            .eq("title", source_data.title)
            .execute()
        )

        if resp.data:
            return resp.data[0]["id"]

        # if not exists, we create the source
        new_source = {
            "title": source_data.title,
            "section": source_data.section,
            "publication_year": source_data.publication_year,
            "source_page": source_data.source_page,
        }
        insert_resp = self.client.table("source").insert(new_source).execute()
        source_id = insert_resp.data[0]["id"]

        # Connect the authors with this new source
        for author_name in source_data.authors:
            author_id = self._get_or_create_author(author_name)
            # Insertar en tabla intermedia source_author
            self.client.table("source_author").insert(
                {"source_id": source_id, "author_id": author_id}
            ).execute()

        return source_id

    def _get_or_create_topic(self, topic_name: str) -> int:
        """It searches for a topic. If it doesn't exist, it creates it and returns its ID."""
        resp = self.client.table("topic").select("id").eq("name", topic_name).execute()
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = self.client.table("topic").insert({"name": topic_name}).execute()
        return insert_resp.data[0]["id"]

    def _get_or_create_requirement(self, req_name: str) -> int:
        """It searches for a requirement. If it doesn't exist, it creates it and returns its ID"""
        resp = (
            self.client.table("requirement").select("id").eq("name", req_name).execute()
        )
        if resp.data:
            return resp.data[0]["id"]

        insert_resp = (
            self.client.table("requirement").insert({"name": req_name}).execute()
        )
        return insert_resp.data[0]["id"]

    # MAIN METHODS OF THE REPOSITORY

    def read(self, exercise_name: str) -> dict:
        response = (
            self.client.table("exercise")
            .select("*")
            .eq("name", exercise_name)
            .execute()
        )
        if not response.data:
            raise ValueError(f"Ejercicio no encontrado: {exercise_name}")
        return response.data[0]

    def read_topic(self, topic: str) -> list:
        raise NotImplementedError()

    def write(self, exercise: Exercise) -> None:
        """It uploads the exercise to the database, assembling all its relationships."""
        # 1. Resolve or create the source and obtain its foreign ID
        source_id = self._get_or_create_source(exercise.source)

        # 2. Prepare and insert the Main Exercise
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

        ex_resp = self.client.table("exercise").insert(db_payload).execute()
        exercise_id = ex_resp.data[0]["id"]  # We obtain the ID of the new exercise

        # 3. Connect Topics (Intermediate Table: exercise_topic)
        for topic_name in exercise.topics:
            topic_id = self._get_or_create_topic(topic_name)
            self.client.table("exercise_topic").insert(
                {"exercise_id": exercise_id, "topic_id": topic_id}
            ).execute()

        # 4. Connect Requirements (Intermediate Table: exercise_requirement)
        for req_name in exercise.requirements:
            req_id = self._get_or_create_requirement(req_name)
            self.client.table("exercise_requirement").insert(
                {"exercise_id": exercise_id, "requirement_id": req_id}
            ).execute()
