import type {
  Exercise,
  ReviewRequest,
  ReviewResponse,
  CategoryResponse,
  PendingExercisesResponse,
  ListExercisesResponse,
  ApiEndpoint,
} from '../types'

const API_BASE = '/api'

async function safeFetch<T>(url: string, options?: RequestInit): Promise<T | null> {
  try {
    const res = await fetch(url, options)
    if (!res.ok) return null
    return res.json()
  } catch {
    return null
  }
}

export class ApiService {
  // Legacy endpoint; prefer fetchExercisesPage (cursor pagination).
  static async fetchPendingExercises(): Promise<Exercise[]> {
    const data = await safeFetch<PendingExercisesResponse>(`${API_BASE}/exercises/pending`)
    return data?.exercises ?? []
  }

  static async fetchExercisesPage(params: {
    limit: number
    afterId: number | null
  }): Promise<ListExercisesResponse | null> {
    const query = new URLSearchParams()
    query.set('limit', String(params.limit))
    if (params.afterId !== null) query.set('after_id', String(params.afterId))
    return safeFetch<ListExercisesResponse>(`${API_BASE}/exercises?${query.toString()}`)
  }

  static async fetchCategories(): Promise<CategoryResponse[]> {
    const data = await safeFetch<CategoryResponse[]>(`${API_BASE}/categories`)
    return data ?? []
  }

  static async fetchApiEndpoints(): Promise<ApiEndpoint[]> {
    const HARDCODED: ApiEndpoint[] = [
      { method: 'GET', path: '/api/health', summary: 'Health check del servidor' },
      { method: 'GET', path: '/api/exercises', summary: 'Lista ejercicios (paginación cursor)' },
      { method: 'GET', path: '/api/exercises/pending', summary: 'Ejercicios pendientes de revisión' },
      { method: 'GET', path: '/api/exercises/{exercise_id}', summary: 'Ejercicio por ID' },
      { method: 'GET', path: '/api/exercises/by-name/{exercise_name}', summary: 'Ejercicio por nombre' },
      { method: 'POST', path: '/api/exercises/{exercise_id}/review', summary: 'Enviar decisión de revisión' },
      { method: 'GET', path: '/api/categories', summary: 'Lista de categorías' },
    ]
    try {
      const res = await fetch('/openapi.json')
      if (!res.ok) return HARDCODED
      const schema: any = await res.json()
      if (!schema?.paths) return HARDCODED
      const endpoints: ApiEndpoint[] = []
      for (const [path, methods] of Object.entries(schema.paths)) {
        for (const [method, detail] of Object.entries(methods as any)) {
          endpoints.push({
            method: method.toUpperCase(),
            path,
            summary: (detail as any).summary ?? '',
          })
        }
      }
      return endpoints.length > 0 ? endpoints : HARDCODED
    } catch {
      return HARDCODED
    }
  }

  static async submitReview(
    exerciseId: number,
    request: ReviewRequest
  ): Promise<ReviewResponse> {
    const data = await safeFetch<ReviewResponse>(
      `${API_BASE}/exercises/${exerciseId}/review`,
      {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(request),
      }
    )
    return data ?? { success: false }
  }
}
