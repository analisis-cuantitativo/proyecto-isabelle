import os
import dotenv
from google.cloud import storage

dotenv.load_dotenv()


def download_from_bucket(bucket_name: str, output_path: str):
    storage_client = storage.Client()
    bucket = storage_client.get_bucket(bucket_name)
    blobs = bucket.list_blobs(max_results=200)

    for blob in blobs:
        if blob.name.endswith("/"):
            continue

        destination_file_name = os.path.join(output_path, blob.name)

        local_dir = os.path.dirname(destination_file_name)

        if not os.path.exists(local_dir):
            print(f"Creating directory {local_dir}")
            os.makedirs(local_dir, exist_ok=True)

        print(f"Downloading {blob.name} to {output_path}/{blob.name}")
        blob.download_to_filename(destination_file_name)


Nombre_Bucket = os.getenv("GCP_BUCKET_NAME")
Path_Output = os.path.abspath("../proyecto-isabelle/old_data")

download_from_bucket(Nombre_Bucket, Path_Output)
print("Download Complete")
