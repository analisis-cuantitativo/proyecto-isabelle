# Isabelle Reviewer

An interactive web-based tool for reviewing and correcting Isabelle/HOL proof exercises.

## Prerequisites

- **Node.js** >= 18
- **Python** >= 3.12
- **Git**

## Quick Start

```powershell
# 1. Run the setup script (installs pnpm, frontend deps, Python venv + deps)
.\setup.ps1

# 2. Activate the Python virtual environment
.\backend\.venv\Scripts\Activate.ps1

# 3. Start both frontend and backend
npm run dev:all
```

The frontend runs at `http://localhost:5173` and the backend at `http://localhost:8000`.

## Configuration

Copy `backend/.env.example` to `backend/.env` and fill in your Supabase credentials:

```
SUPABASE_URL=https://your-project.supabase.co
SUPABASE_KEY=your-anon-or-service-key
DIRECT_CONNECTION_STRING=postgresql://postgres:YOUR_PASSWORD@db.your-project.supabase.co:5432/postgres
```

## Manual Setup

If you prefer to set up step by step:

```powershell
# Install pnpm
npm install -g pnpm

# Install frontend dependencies
pnpm install

# Create Python virtual environment
python -m venv backend\.venv

# Activate it
.\backend\.venv\Scripts\Activate.ps1

# Install backend dependencies
pip install -r backend\requirements.txt

# Start both servers
npm run dev:all
```

## Project Structure

```
isabelle/
├── backend/
│   ├── app/
│   │   ├── models/          # Pydantic DTOs
│   │   ├── routers/         # FastAPI route handlers
│   │   └── services/        # Business logic
│   ├── main.py              # FastAPI application entry point
│   └── requirements.txt     # Python dependencies
├── src/
│   ├── components/          # React UI components
│   ├── hooks/               # React hooks (state, keyboard shortcuts, theme)
│   ├── services/            # API client
│   ├── types/               # TypeScript type definitions
│   └── utils/               # Utility functions (diff, etc.)
├── setup.ps1                # Automated setup script
└── package.json             # Node.js scripts and dependencies
```

## Available Scripts

| Command | Description |
|---------|-------------|
| `npm run dev:all` | Start both frontend and backend |
| `npm run dev:frontend` | Start Vite dev server only |
| `npm run dev:backend` | Start Uvicorn backend only |
| `npm run build` | TypeScript check + Vite production build |
