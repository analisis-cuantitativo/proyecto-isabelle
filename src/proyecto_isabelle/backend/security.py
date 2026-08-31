import os
import secrets

from fastapi import Depends, HTTPException, status
from fastapi.security import HTTPBasic, HTTPBasicCredentials

# auto_error=False so FastAPI doesn't inject a WWW-Authenticate: Basic header
# on missing credentials — that header makes browsers pop their own native
# login dialog on top of the app's own Login screen.
security = HTTPBasic(auto_error=False)


def verify_credentials(
    credentials: HTTPBasicCredentials | None = Depends(security),
) -> str:
    expected_username = os.getenv("AUTH_USERNAME", "admin")
    expected_password = os.getenv("AUTH_PASSWORD", "admin")

    is_valid = credentials is not None and (
        secrets.compare_digest(credentials.username, expected_username)
        and secrets.compare_digest(credentials.password, expected_password)
    )

    if not is_valid:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Usuario o contrasena incorrectos",
        )

    return credentials.username
