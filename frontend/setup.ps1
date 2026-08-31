# Isabelle Reviewer — Setup Script
# Run: .\setup.ps1
# Detects what's installed and only installs what's missing.

$ErrorActionPreference = "Stop"
$ROOT = Split-Path -Parent $MyInvocation.MyCommand.Path

Write-Host "=== Isabelle Reviewer Setup ===" -ForegroundColor Cyan
Write-Host ""

# ── 1. pnpm ──────────────────────────────────────────────────────────────
if (!(Get-Command pnpm -ErrorAction SilentlyContinue)) {
  Write-Host "[1/3] Instalando pnpm..." -ForegroundColor Yellow
  npm install -g pnpm
  if ($LASTEXITCODE -ne 0) { throw "pnpm installation failed" }
} else {
  $v = (pnpm --version)
  Write-Host "[1/3] pnpm $v ya instalado" -ForegroundColor Green
}

# ── 2. Frontend dependencies ────────────────────────────────────────────
Write-Host "[2/3] Instalando dependencias del frontend..." -ForegroundColor Yellow
Set-Location $ROOT
pnpm install
if ($LASTEXITCODE -ne 0) { throw "pnpm install failed" }

# ── 3. Python virtual environment + backend dependencies ────────────────
$VENV = Join-Path $ROOT "backend\.venv"
$PIP = Join-Path $VENV "Scripts\pip.exe"
$ACTIVATE_SCRIPT = Join-Path $VENV "Scripts\Activate.ps1"

if (!(Test-Path $VENV)) {
  Write-Host "[3/3] Creando entorno virtual de Python..." -ForegroundColor Yellow
  python -m venv $VENV
  if ($LASTEXITCODE -ne 0) { throw "venv creation failed" }
} else {
  Write-Host "[3/3] Entorno virtual ya existe" -ForegroundColor Green
}

Write-Host "[3/3] Instalando dependencias del backend..." -ForegroundColor Yellow
& $PIP install -r "$ROOT\backend\requirements.txt"
if ($LASTEXITCODE -ne 0) { throw "pip install failed" }

# ── 4. .env check ───────────────────────────────────────────────────────
$ENV_FILE = Join-Path $ROOT "backend\.env"
if (!(Test-Path $ENV_FILE)) {
  Write-Host ""
  Write-Host "⚠ ADVERTENCIA: No se encuentra backend\.env" -ForegroundColor Red
  Write-Host "  Copia backend\.env.example a backend\.env y completa las variables." -ForegroundColor Yellow
} else {
  $key = Select-String -Path $ENV_FILE -Pattern "SUPABASE_KEY=" -SimpleMatch
  if (!$key -or ($key -match "SUPABASE_KEY=$")) {
    Write-Host ""
    Write-Host "⚠ ADVERTENCIA: SUPABASE_KEY vacia en backend\.env" -ForegroundColor Yellow
    Write-Host "  Edita backend\.env y coloca tu clave de Supabase." -ForegroundColor Yellow
  } else {
    Write-Host ""
    Write-Host ".env OK" -ForegroundColor Green
  }
}

# ── Done ────────────────────────────────────────────────────────────────
Write-Host ""
Write-Host "=== Setup completado ===" -ForegroundColor Cyan
Write-Host ""
Write-Host "Para iniciar el proyecto ejecuta:" -ForegroundColor White
Write-Host "  .\backend\.venv\Scripts\Activate.ps1" -ForegroundColor Gray
Write-Host "  npm run dev:all" -ForegroundColor Gray
Write-Host ""
Write-Host "O en otro terminal (sin activar venv):" -ForegroundColor White
Write-Host "  npm run dev:all" -ForegroundColor Gray
