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

Después de esto, ya se podrá correr el `scripts/e2e.py`.
Para poder usarlo, necesitarán exportar las llaves que están
en el `.env` file. Eso lo pueden hacer con:
```bash
set -a && source .env && set +a
```
