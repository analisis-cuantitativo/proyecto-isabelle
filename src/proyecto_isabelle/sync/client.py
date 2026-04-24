"""GCS client wrapper with lazy-loaded bucket connection."""

from google.cloud import storage

from proyecto_isabelle.sync.config import get_config


class GCSClient:
    """Wrapper around Google Cloud Storage client with lazy bucket loading."""

    def __init__(self, bucket_name: str | None = None) -> None:
        """Initialize the GCS client.

        Args:
            bucket_name: Name of the GCS bucket. If not provided, reads from
                         GCP_BUCKET_NAME environment variable.
        """
        self._bucket_name = bucket_name
        self._client: storage.Client | None = None
        self._bucket: storage.Bucket | None = None

    @property
    def bucket_name(self) -> str:
        """Get the bucket name, loading from config if necessary."""
        if self._bucket_name is None:
            config = get_config()
            if config.gcp_bucket_name is None:
                raise ValueError(
                    "GCP_BUCKET_NAME not set. Set it in .env or pass bucket_name."
                )
            self._bucket_name = config.gcp_bucket_name
        return self._bucket_name

    @property
    def client(self) -> storage.Client:
        """Get the GCS client, creating it lazily."""
        if self._client is None:
            self._client = storage.Client()
        return self._client

    @property
    def bucket(self) -> storage.Bucket:
        """Get the bucket, loading it lazily."""
        if self._bucket is None:
            self._bucket = self.client.bucket(self.bucket_name)
        return self._bucket

    def blob(self, blob_name: str) -> storage.Blob:
        """Get a blob object for the given name."""
        return self.bucket.blob(blob_name)

    def list_blobs(self, prefix: str | None = None) -> list[storage.Blob]:
        """List all blobs in the bucket, optionally filtered by prefix."""
        return list(self.client.list_blobs(self.bucket, prefix=prefix))
