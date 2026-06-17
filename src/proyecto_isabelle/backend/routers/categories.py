from fastapi import APIRouter, HTTPException

router = APIRouter(prefix="/api/categories", tags=["categories"])


@router.get("")
async def list_categories():
    raise HTTPException(status_code=501, detail="categories endpoint not yet implemented")
