import { useState, useEffect, useCallback, useRef } from 'react'
import { ApiService } from '../services/api'
import { generatePatch } from '../utils/diff'
import type { Exercise, ReviewResponse } from '../types'

const EXERCISE_CACHE_KEY = 'exercise_cache_v1'
const PAGE_SIZE = 30

function safeParseJSON<T>(value: string | null): T | null {
  if (!value) return null
  try {
    return JSON.parse(value) as T
  } catch {
    return null
  }
}

type CachedExercises = {
  exercises: Exercise[]
  next_after_id: number | null
  saved_at: number
}

export function useExercises() {
  const [exercises, setExercises] = useState<Exercise[]>([])
  const [currentIndex, setCurrentIndex] = useState(0)
  const [reviewedStack, setReviewedStack] = useState<Exercise[]>([])
  const [isLoading, setIsLoading] = useState(true)
  const [isUsingFallback, setIsUsingFallback] = useState(false)
  const [apiError, setApiError] = useState<string | null>(null)
  const [reviewFeedback, setReviewFeedback] = useState<ReviewResponse | null>(null)
  const [verifiedCode, setVerifiedCode] = useState<string | null>(null)
  const [isVerifying, setIsVerifying] = useState(false)
  const [hasMore, setHasMore] = useState(true)
  const [isLoadingMore, setIsLoadingMore] = useState(false)

  const nextAfterIdRef = useRef<number | null>(null)
  const isFetchingRef = useRef(false)

  const persistCache = useCallback((payload: CachedExercises) => {
    try {
      localStorage.setItem(EXERCISE_CACHE_KEY, JSON.stringify(payload))
    } catch {
      // ignore storage quota errors
    }
  }, [])

  const loadFirstPage = useCallback(async () => {
    try {
      setIsLoading(true)
      setApiError(null)

      const cached = safeParseJSON<CachedExercises>(
        localStorage.getItem(EXERCISE_CACHE_KEY)
      )
      if (cached?.exercises?.length) {
        setExercises(cached.exercises)
        nextAfterIdRef.current = cached.next_after_id
        setHasMore(cached.next_after_id !== null)
        setIsUsingFallback(false)
        setIsLoading(false)
        return
      }

      const page = await ApiService.fetchExercisesPage({ limit: PAGE_SIZE, afterId: null })
      const exData = page?.exercises ?? []
      if (exData.length === 0) {
        setExercises([])
        setHasMore(false)
        setIsUsingFallback(true)
        setApiError(null)
      } else {
        setExercises(exData)
        nextAfterIdRef.current = page?.next_after_id ?? null
        setHasMore(nextAfterIdRef.current !== null)
        setIsUsingFallback(false)
        setApiError(null)
        persistCache({ exercises: exData, next_after_id: nextAfterIdRef.current, saved_at: Date.now() })
      }
    } catch (_err) {
      setExercises([])
      setHasMore(false)
      setIsUsingFallback(false)
      setApiError('Error de conexion. Inicia el backend para conectarte a Supabase.')
    } finally {
      setIsLoading(false)
    }
  }, [persistCache])

  const fetchNextPage = useCallback(async () => {
    if (isFetchingRef.current) return
    if (nextAfterIdRef.current === null) return

    isFetchingRef.current = true
    setIsLoadingMore(true)
    try {
      const page = await ApiService.fetchExercisesPage({
        limit: PAGE_SIZE,
        afterId: nextAfterIdRef.current,
      })
      const newItems = page?.exercises ?? []
      if (newItems.length === 0) {
        nextAfterIdRef.current = null
        setHasMore(false)
        return
      }

      nextAfterIdRef.current = page?.next_after_id ?? null
      setHasMore(nextAfterIdRef.current !== null)

      setExercises(prev => {
        const merged = [...prev]
        const seen = new Set<number>()
        for (const ex of merged) {
          if (typeof ex.id === 'number') seen.add(ex.id)
        }
        for (const ex of newItems) {
          if (typeof ex.id === 'number' && seen.has(ex.id)) continue
          merged.push(ex)
        }
        persistCache({ exercises: merged, next_after_id: nextAfterIdRef.current, saved_at: Date.now() })
        return merged
      })
    } finally {
      isFetchingRef.current = false
      setIsLoadingMore(false)
    }
  }, [persistCache])

  useEffect(() => {
    loadFirstPage()
  }, [loadFirstPage])

  const currentExercise = exercises[currentIndex] ?? null

  const currentCode =
    currentExercise?.corrected_thy_code ??
    currentExercise?.proposed_thy_code ??
    ''

  const isApproveEnabled = verifiedCode !== null && verifiedCode === currentCode

  const handleVerify = useCallback(async () => {
    if (!currentExercise) return
    setIsVerifying(true)
    try {
      const result = await ApiService.verifyCode(currentExercise.id, currentCode)
      setReviewFeedback(result ? { success: result.verified, isabelle_validation: result } : null)
      if (result?.verified) {
        setVerifiedCode(currentCode)
      }
    } finally {
      setIsVerifying(false)
    }
  }, [currentExercise, currentCode])

  const handleCodeChange = useCallback(
    (newCode: string) => {
      setExercises(prev => {
        const updated = [...prev]
        if (updated[currentIndex]) {
          updated[currentIndex] = { ...updated[currentIndex], corrected_thy_code: newCode }
        }
        return updated
      })
    },
    [currentIndex]
  )

  const handleReview = useCallback(
    async (decision: 'approved' | 'rejected') => {
      if (!currentExercise) return
      if (decision === 'approved' && !isApproveEnabled) return

      setReviewFeedback(null)
      setVerifiedCode(null)
      const history = currentExercise.history ?? []
      const baseCode = currentExercise.proposed_thy_code ?? ''
      const lastCode = history.length > 0 ? history[history.length - 1].full_code : baseCode

      let updatedHistory = history
      if (lastCode !== currentCode) {
        const diff = generatePatch(lastCode, currentCode)
        const time = new Date().toLocaleTimeString()
        updatedHistory = [
          ...history,
          { time, diff, full_code: currentCode, decision },
        ]
      }

      const reviewedExercise: Exercise = {
        ...currentExercise,
        decision,
        history: updatedHistory,
        is_verified: decision === 'approved',
      }

      setReviewedStack(prev => [...prev, reviewedExercise])

      setExercises(prev => {
        const newList = [...prev]
        newList[currentIndex] = reviewedExercise
        return newList
      })

      setCurrentIndex(prev => prev + 1)

      // Prefetch next page when approaching the end of the cache
      if (currentIndex >= exercises.length - 6) {
        fetchNextPage()
      }

      // Llamada al backend (sin diff ni time en el payload)
      try {
        const result = await ApiService.submitReview(currentExercise.id ?? 0, {
          decision,
          corrected_thy_code: currentCode,
        })
        setReviewFeedback(result)
      } catch (_err) {
        // El diff y el historial se mantienen locales aunque falle el backend
      }
    },
    [currentExercise, currentIndex, currentCode, exercises.length, fetchNextPage, isApproveEnabled]
  )

  const handleSkip = useCallback(() => {
    if (currentIndex >= exercises.length - 1) return
    setCurrentIndex(prev => prev + 1)
    setReviewFeedback(null)
    setVerifiedCode(null)
  }, [currentIndex, exercises.length])

  const handlePrevious = useCallback(() => {
    if (currentIndex <= 0) return
    setCurrentIndex(prev => prev - 1)
    setReviewFeedback(null)
    setVerifiedCode(null)
  }, [currentIndex])

  const handleUndo = useCallback(() => {
    if (reviewedStack.length === 0) return
    setReviewedStack(prev => prev.slice(0, -1))
    setCurrentIndex(prev => prev - 1)
    setReviewFeedback(null)
    setVerifiedCode(null)
  }, [reviewedStack])

  const jumpToExercise = useCallback(
    (exerciseId: number) => {
      const idx = exercises.findIndex(ex => ex.id === exerciseId)
      if (idx === -1) return
      setCurrentIndex(idx)
      setReviewFeedback(null)
      setVerifiedCode(null)
    },
    [exercises]
  )

  const isQueueEmpty = currentIndex >= exercises.length

  useEffect(() => {
    if (isQueueEmpty) {
      fetchNextPage()
    } else if (currentIndex >= exercises.length - 6) {
      fetchNextPage()
    }
  }, [currentIndex, exercises.length, fetchNextPage, isQueueEmpty])

  return {
    exercises,
    currentExercise,
    currentCode,
    isLoading,
    isUsingFallback,
    apiError,
    reviewFeedback,
    reviewedStack,
    currentIndex,
    isQueueEmpty,
    isApproveEnabled,
    isVerifying,
    hasMore,
    isLoadingMore,
    handleCodeChange,
    handleReview,
    handleVerify,
    handleSkip,
    handlePrevious,
    handleUndo,
    jumpToExercise,
    loadMore: fetchNextPage,
    retryFetch: loadFirstPage,
  }
}
