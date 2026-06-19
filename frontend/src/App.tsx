import { useState, useCallback } from 'react'
import { Database, History, Play, X } from 'lucide-react'
import { useTheme } from './hooks/useTheme'
import { useExercises } from './hooks/useExercises'
import { useKeyboardShortcuts } from './hooks/useKeyboardShortcuts'
import { Sidebar } from './components/Sidebar'
import { Header } from './components/Header'
import { ExerciseCard } from './components/ExerciseCard'
import { IsabelleEditor } from './components/IsabelleEditor'
import { HistoryPanel } from './components/HistoryPanel'
import { ReviewControls } from './components/ReviewControls'
import { QueueEmpty } from './components/QueueEmpty'
import type { ReviewResponse } from './types'

function ValidationFeedback({ feedback }: { feedback: ReviewResponse | null }) {
  if (!feedback?.isabelle_validation) return null

  const { is_valid, errors, warnings } = feedback.isabelle_validation

  return (
    <div
      className={`mt-4 p-4 rounded-xl border text-sm space-y-2 animate-fade-in ${
        is_valid
          ? 'bg-emerald-500/10 border-emerald-500/20 text-emerald-700 dark:text-emerald-400'
          : 'bg-rose-500/10 border-rose-500/20 text-rose-700 dark:text-rose-400'
      }`}
    >
      <p className="font-semibold">
        {is_valid ? 'Validacion Isabelle: OK' : 'Validacion Isabelle: Errores encontrados'}
      </p>
      {errors.length > 0 && (
        <ul className="list-disc list-inside space-y-1">
          {errors.map((e, i) => (
            <li key={i}>{e}</li>
          ))}
        </ul>
      )}
      {warnings.length > 0 && (
        <ul className="list-disc list-inside text-amber-600 dark:text-amber-400 space-y-1">
          {warnings.map((w, i) => (
            <li key={i}>{w}</li>
          ))}
        </ul>
      )}
    </div>
  )
}

export default function App() {
  const { theme, toggleTheme } = useTheme()
  const {
    categories,
    currentExercise,
    currentCode,
    exercises,
    isLoading,
    isUsingFallback,
    apiError,
    reviewFeedback,
    reviewedStack,
    currentIndex,
    isQueueEmpty,
    handleCodeChange,
    handleReview,
    handleSkip,
    handlePrevious,
    handleUndo,
    retryFetch,
  } = useExercises()

  const [showHistory, setShowHistory] = useState(false)
  const [sidebarOpen, setSidebarOpen] = useState(true)
  const [dismissFallback, setDismissFallback] = useState(false)

  const onApprove = useCallback(() => handleReview('approved'), [handleReview])
  const onReject = useCallback(() => handleReview('rejected'), [handleReview])
  const onSkip = useCallback(() => handleSkip(), [handleSkip])
  const onPrevious = useCallback(() => handlePrevious(), [handlePrevious])
  const toggleSidebar = useCallback(() => setSidebarOpen(prev => !prev), [])

  useKeyboardShortcuts(
    { onApprove, onReject, onSkip, onPrevious, onUndo: handleUndo },
    !isQueueEmpty
  )

  if (isLoading) {
    return (
      <div className="flex h-screen items-center justify-center bg-slate-50 dark:bg-zinc-950 text-slate-900 dark:text-slate-100">
        <div className="animate-pulse text-slate-400">Cargando ejercicios desde la API...</div>
      </div>
    )
  }

  if (apiError && exercises.length === 0) {
    return (
      <div className="flex h-screen items-center justify-center bg-slate-50 dark:bg-zinc-950 text-slate-900 dark:text-slate-100">
        <div className="text-center space-y-4 bg-white/60 dark:bg-zinc-900/60 backdrop-blur-xl rounded-2xl p-8 border border-white/60 dark:border-white/10 shadow-xl">
          <p className="text-slate-500 font-medium">{apiError}</p>
          <button
            onClick={retryFetch}
            className="px-4 py-2 bg-blue-500/10 text-blue-700 dark:text-blue-300 border border-blue-500/20 rounded-xl hover:bg-blue-500/20 transition-all duration-500 ease-out"
          >
            Reintentar
          </button>
        </div>
      </div>
    )
  }

  return (
    <div className="min-h-screen bg-slate-50 dark:bg-zinc-950 text-slate-900 dark:text-slate-100 font-sans transition-colors duration-500 ease-out flex relative isolate">

      <div className="fixed inset-0 overflow-hidden pointer-events-none -z-10" aria-hidden="true">
        <div className="absolute -top-[20%] -left-[10%] w-[50%] h-[50%] rounded-full bg-blue-400/20 dark:bg-blue-600/10 blur-[120px] animate-float" />
        <div className="absolute top-[60%] -right-[10%] w-[40%] h-[60%] rounded-full bg-emerald-400/20 dark:bg-emerald-600/10 blur-[120px] animate-float-delayed" />
        <div className="absolute top-[20%] left-[60%] w-[30%] h-[40%] rounded-full bg-purple-400/20 dark:bg-purple-600/10 blur-[120px] animate-float-slow" />
      </div>

      <Sidebar
        open={sidebarOpen}
        categories={categories}
        reviewedCount={reviewedStack.length}
        totalExercises={
          reviewedStack.length + (currentExercise ? 1 : 0)
        }
        hasVerified={reviewedStack.some(e => e.is_verified)}
      />

      <main className="flex-1 flex flex-col h-screen overflow-hidden">
        <Header
          theme={theme}
          onToggleTheme={toggleTheme}
          title={currentExercise?.name}
          topic={currentExercise?.topics?.[0]}
          sidebarOpen={sidebarOpen}
          onToggleSidebar={toggleSidebar}
        />

        <div className="flex-1 overflow-y-auto p-8 flex justify-center">
          <div className="w-full max-w-4xl flex flex-col gap-8 pb-12">
            {isUsingFallback && !apiError && !dismissFallback && (
              <div className="flex items-center gap-3 px-5 py-3 rounded-2xl bg-amber-500/10 border border-amber-500/20 text-amber-700 dark:text-amber-300 text-sm shadow-sm animate-fade-in transition-all duration-500 ease-out hover:scale-[1.01] hover:shadow-lg">
                <Database className="w-5 h-5 shrink-0" />
                <span className="flex-1">Base de datos vac&iacute;a &mdash; no hay ejercicios disponibles.</span>
                <button
                  onClick={() => setDismissFallback(true)}
                  className="shrink-0 p-1 rounded-lg hover:bg-amber-500/20 transition-all duration-300"
                  aria-label="Cerrar advertencia"
                >
                  <X className="w-4 h-4" />
                </button>
              </div>
            )}
            {isQueueEmpty ? (
              <QueueEmpty
                canUndo={reviewedStack.length > 0}
                onUndo={handleUndo}
              />
            ) : currentExercise ? (
              <>
                <ExerciseCard statement={currentExercise.statement ?? ''} />

                <section className="flex flex-col gap-4">
                  <div className="flex items-center justify-between px-2">
                    <h2 className="text-xs font-bold text-slate-400 dark:text-slate-500 uppercase tracking-widest flex items-center gap-2">
                      <Play className="w-4 h-4" /> Codigo Isabelle
                    </h2>
                    <button
                      onClick={() => setShowHistory(!showHistory)}
                      className={`flex items-center gap-2 text-sm px-4 py-2 rounded-xl border transition-all duration-500 ease-out ${
                        showHistory
                          ? 'bg-blue-500/10 text-blue-700 dark:text-blue-300 border-blue-500/20 shadow-inner'
                          : 'bg-white/40 dark:bg-white/5 border-white/50 dark:border-white/10 hover:bg-white/60 dark:hover:bg-white/10 text-slate-600 dark:text-slate-400 shadow-sm'
                      }`}
                      aria-expanded={showHistory}
                    >
                      <History className="w-4 h-4" />
                      Historial ({currentExercise.history?.length ?? 0})
                    </button>
                  </div>

                  <div className="flex gap-4">
                    <div className="flex-1">
                      <IsabelleEditor
                        code={currentCode}
                        onChange={handleCodeChange}
                      />
                      <ValidationFeedback feedback={reviewFeedback} />
                    </div>

                    {showHistory && (
                      <div className="w-80 bg-white/60 dark:bg-zinc-900/60 backdrop-blur-2xl border border-white/50 dark:border-white/10 rounded-2xl p-4 overflow-y-auto h-96 shadow-2xl animate-slide-in">
                        <h3 className="text-xs font-bold text-slate-400 dark:text-slate-500 uppercase tracking-widest mb-4">
                          Historial de Cambios
                        </h3>
                        <HistoryPanel history={currentExercise.history ?? []} />
                      </div>
                    )}
                  </div>
                </section>

                <ReviewControls
                  onApprove={onApprove}
                  onReject={onReject}
                  onSkip={onSkip}
                  onPrevious={onPrevious}
                  onUndo={handleUndo}
                  canUndo={reviewedStack.length > 0}
                  canSkip={currentIndex < exercises.length - 1}
                  canPrevious={currentIndex > 0}
                />
              </>
            ) : null}
          </div>
        </div>
      </main>
    </div>
  )
}
