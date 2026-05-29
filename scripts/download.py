from dotenv import load_dotenv
from pathlib import Path
from os import getenv
from google.cloud import storage
from proyecto_isabelle.util.constants import ROOT_DIR

load_dotenv()


def download_from_bucket(bucket_name: str, output_path: Path) -> None:
    storage_client = storage.Client()
    bucket = storage_client.get_bucket(bucket_name)
    blobs = bucket.list_blobs(max_results=200)

    for blob in blobs:
        if blob.name.endswith("/"):
            continue

        destination_file_name = Path.join(output_path, blob.name)

        local_dir = Path.dirname(destination_file_name)

        if not Path.exists(local_dir):
            print(f"Creating directory {local_dir}")
            Path.makedirs(local_dir, exist_ok=True)

        print(f"Downloading {blob.name} to {output_path}/{blob.name}")
        blob.download_to_filename(destination_file_name)


nombre_bucket = getenv("GCP_BUCKET_NAME")
path_output = ROOT_DIR / "old_data"

download_from_bucket(nombre_bucket, path_output)
print("Download Complete")
