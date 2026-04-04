"""
Este script es un ejemplo de cómo enviar una prueba al servidor
que está corriendo Isabelle.

Primero, tienen que arrancar el servidor usando `docker-compose`:

```bash
docker-compose up
```

Si es la primera vez que lo hacen, tomará un tiempo.

Después, ya pueden usar este script. En este, se cargará un
ejemplo.thy y se enviarán sus contenidos a Isabelle para verificar.
"""

from pathlib import Path

from proyecto_isabelle.query import isabelle

ROOT_DIR = Path(__file__).parent.parent

example_path = ROOT_DIR / "data" / "raw" / "isabelle" / "example.thy"

res = isabelle.query_file(example_path)

print(res)
