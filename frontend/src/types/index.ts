export type ReviewDecision = 'approved' | 'rejected'
export type DiffLineType = 'added' | 'removed'

export interface DiffLine {
  type: DiffLineType
  text: string
}

export interface HistoryEntry {
  time: string
  diff: DiffLine[]
  full_code: string
  decision: ReviewDecision
}

export interface Source {
  title: string
  authors: string[]
  section: string
  publication_year: number
  source_page: string
}

export interface Exercise {
  id: number
  name: string
  source: Source
  topics: string[]
  requirements: string[] | null
  is_verified: boolean
  msc_code?: string | null
  license?: string | null
  proposed_thy_code?: string | null
  corrected_thy_code?: string | null
  statement?: string | null
  proof?: string | null

  // Local-only UI state
  history?: HistoryEntry[]
  decision?: ReviewDecision
}

export interface ReviewRequest {
  decision: ReviewDecision
  corrected_thy_code: string
}

export interface IsabelleValidationResult {
  is_valid: boolean
  errors: string[]
  warnings: string[]
}

export interface ReviewResponse {
  success: boolean
  isabelle_validation?: IsabelleValidationResult
}

export interface CategoryResponse {
  name: string
  exercise_count: number
}

export interface PendingExercisesResponse {
  exercises: Exercise[]
  total: number
}

export interface ListExercisesResponse {
  exercises: Exercise[]
  total: number | null
  next_after_id: number | null
}

export interface ApiEndpoint {
  method: string
  path: string
  summary: string
}
