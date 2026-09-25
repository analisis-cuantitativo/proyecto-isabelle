# Proyecto: Agentes para la demostración automática de teoremas en Isabelle

En este proyecto investigaremos si los agentes y LLM actuales pueden ayudarnos a demostrar teoremas de forma automática en Isabelle.

## Prerequisitios para contribuir

- Instalar [`uv`](https://docs.astral.sh/uv/getting-started/installation/).
- Instalar [`prek`](https://github.com/j178/prek?tab=readme-ov-file#installation).
- Instalar [`docker`](https://www.docker.com/get-started/).

Para instalar todas las dependencias y para dejar listo los _pre-commit hooks_, correr en la terminal:

```bash
uv sync
prek install
```

Además, para poder correr el servidor de Isabelle, necesitarás tener `docker` instalado y el submódulo importado. Para hacerlo, es necesario correr
```bash
git submodule update --init --recursive
```

Construyamos la imagen de DeepIsaHOL yendo a su carpeta y
construyéndola:
```bash
cd DeepIsaHOL
docker-compose up
```

Por defecto esto es rápido (segundos): la imagen solo trae la lógica base
`HOL`, que Isabelle ya distribuye pre-compilada. Si tu trabajo necesita
librerías adicionales (análisis real, probabilidad, teoría de números,
álgebra, ...), tienes que pedirlas explícitamente -- ver la sección
"Configurando qué librerías de Isabelle se compilan" más abajo.

Después de esto, ya se podrá correr el `scripts/e2e.py`.
Para poder usarlo, necesitarán exportar las llaves que están
en el `.env` file. Eso lo pueden hacer con:
```bash
set -a && source .env && set +a
```

El `.env` file debería lucir así:
```bash
ANTHROPIC_API_KEY=...
OPENAI_API_KEY=...
GCP_BUCKET_NAME=proofs-dataset
SUPABASE_URL=...
SUPABASE_KEY=...
SUPABASE_EMAIL=...
SUPABASE_PASSWORD=...
DIRECT_CONNECTION_STRING=...
```

## Configurando qué librerías de Isabelle se compilan

La imagen de `DeepIsaHOL` compila, dentro de Docker, una sesión llamada
`Benchmark` que agrupa las librerías de Isabelle que el servidor tiene
disponibles (para el endpoint `/build`, y para que un `.thy` generado pueda
hacer `imports` de ellas sin disparar una compilación al vuelo). Qué entra en
esa sesión se controla con dos variables de entorno, pasadas como
build-args de Docker:

- `DEEPISAHOL_PARENT_SESSION` (por defecto `HOL`) -- la sesión padre de la
  que `Benchmark` extiende. `HOL` viene ya compilada con la distribución de
  Isabelle, así que con el valor por defecto este paso del build es
  prácticamente instantáneo.
- `DEEPISAHOL_EXTRA_SESSIONS` (por defecto vacío) -- lista de sesiones
  hermanas, separadas por comas, que se compilan y se cargan junto al padre.
  Cada nombre debe estar en la tabla `UMBRELLA_THEORIES` de
  `DeepIsaHOL/benchmark/gen_root.py`; si no lo está, el build falla con un
  mensaje que lista las sesiones soportadas.

Se pasan como cualquier build-arg de `docker compose`, por variables de
entorno o en un `.env`:

```bash
DEEPISAHOL_PARENT_SESSION=HOL \
DEEPISAHOL_EXTRA_SESSIONS= \
docker compose build deepisahol   # build mínimo (segundos)
```

Para reproducir el heap "completo" que este proyecto usaba antes de esta
configuración (análisis real, probabilidad, teoría de números, álgebra,
combinatoria, cardinales, `HOL-Decision_Procs`/`real_asymp`/`sos`, ...), que
tarda del orden de 1-2 horas:

```bash
DEEPISAHOL_PARENT_SESSION=HOL-Probability \
DEEPISAHOL_EXTRA_SESSIONS=HOL-Number_Theory,HOL-Algebra,HOL-Combinatorics,HOL-Cardinals,HOL-Computational_Algebra,HOL-Decision_Procs,HOL-Real_Asymp,HOL-Eisbach,HOL-Library \
docker compose build deepisahol
```

Guía rápida de qué pedir según lo que necesites:

| Necesitas... | Añade a `DEEPISAHOL_EXTRA_SESSIONS` (o cambia el padre) |
|---|---|
| Análisis real (límites, continuidad, derivadas, integrales) | padre `HOL-Analysis`, o `HOL-Probability` si también necesitas probabilidad |
| Probabilidad | padre `HOL-Probability` |
| Teoría de números | `HOL-Number_Theory` |
| Álgebra abstracta (grupos, anillos, cuerpos) | `HOL-Algebra` |
| Combinatoria | `HOL-Combinatorics` |
| Cardinales | `HOL-Cardinals` |
| Álgebra computacional (polinomios, etc.) | `HOL-Computational_Algebra` |
| El método `approximation` | `HOL-Decision_Procs` |
| El método `real_asymp` | `HOL-Real_Asymp` |
| El método `eisbach` (definir tácticas nuevas) | `HOL-Eisbach` |
| El método `sos`, discriminante cuadrático, numerales ejecutables | `HOL-Library` |

El servidor en ejecución siempre reporta, en vivo, con qué sesiones fue
compilado su heap `Benchmark` en `GET /sessions` -- si esta tabla y el
servidor desplegado alguna vez difieren, `/sessions` es la fuente de verdad
(la usa automáticamente `proyecto_isabelle.query.isabelle` para saber qué
puede pedir en un `imports`).

La compilación en sí (`isabelle build -b -o system_heaps ... -D
DeepIsaHOL/benchmark`) queda documentada con más detalle en los comentarios
de `DeepIsaHOL/Dockerfile`, incluyendo las variables `BENCHMARK_THREADS` /
`BENCHMARK_JOBS` que controlan su paralelismo (solo relevantes cuando
`DEEPISAHOL_EXTRA_SESSIONS` no está vacío).

## Backend API

Servidor FastAPI con los endpoints REST. Para correrlo:

```bash
uv sync
uv run uvicorn proyecto_isabelle.backend.main:app --reload --port 8000
```

Si tienes problemas con la versión de Python (≥3.13 requerida), usa el workaround con `PYTHONPATH`:

```bash
$env:PYTHONPATH = "src"
uv run uvicorn proyecto_isabelle.backend.main:app --reload --port 8000
```

### Endpoints

| Método | Ruta | Descripción |
|--------|------|-------------|
| GET | `/api/health` | Health check |
| GET | `/api/exercises?limit=50&after_id=` | Lista ejercicios (paginación cursor) |
| GET | `/api/exercises/pending` | Ejercicios pendientes de revisión |
| GET | `/api/exercises/{id}` | Ejercicio por ID |
| GET | `/api/exercises/by-name/{name}` | Ejercicio por nombre |
| POST | `/api/exercises/{id}/review` | Enviar decisión (`approved`/`rejected`) |
| GET | `/api/categories` | Lista categorías |
