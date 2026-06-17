from proyecto_isabelle.sync.repository import SupabaseRepository


def main():
    print("Conectando a Supabase...")

    try:
        repo = SupabaseRepository()
        client = repo.client
    except ValueError as e:
        print(f"[ERROR] {e}")
        return
    except Exception as e:
        print(f"[ERROR] No se pudo conectar a Supabase: {e}")
        return

    ex_resp = client.table("exercise").select("id", count="exact").execute()
    count = getattr(ex_resp, "count", None)
    total_exercises = count if isinstance(count, int) else len(ex_resp.data or [])

    if total_exercises == 0:
        print("Base de datos vacia — 0 ejercicios encontrados.")
        return

    print(f"Ejercicios encontrados: {total_exercises}")

    top = client.table("exercise").select("id,name,is_verified").order("id").limit(10).execute()
    print("Primeros 10:")
    for row in top.data or []:
        verified = "✓" if row.get("is_verified") else "✗"
        print(f"  [{row['id']:>4}] {verified} {row['name']}")

    for table, label in [
        ("source", "Fuentes"),
        ("author", "Autores"),
        ("topic", "Topicos"),
        ("requirement", "Requisitos"),
    ]:
        resp = client.table(table).select("id", count="exact").execute()
        count = resp.count if hasattr(resp, "count") else len(resp.data or [])
        print(f"  {label}: {count}")

    if total_exercises > 10:
        remaining = total_exercises - 10
        print(f"... y {remaining} ejercicio(s) mas.")


if __name__ == "__main__":
    main()
