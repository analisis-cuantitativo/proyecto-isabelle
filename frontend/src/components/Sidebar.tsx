import { useEffect, useState } from 'react'
import { Terminal, Loader2 } from 'lucide-react'
import { ApiService } from '../services/api'
import type { ApiEndpoint, Exercise } from '../types'

interface SidebarProps {
  open: boolean
  exercises: Exercise[]
  currentExerciseId: number | null
  onSelectExercise: (id: number) => void
  hasMore: boolean
  onLoadMore: () => void
  isLoadingMore: boolean
  reviewedCount: number
  totalExercises: number
}

export function Sidebar({
  open,
  exercises,
  currentExerciseId,
  onSelectExercise,
  hasMore,
  onLoadMore,
  isLoadingMore,
  reviewedCount,
  totalExercises,
}: SidebarProps) {
  const [endpoints, setEndpoints] = useState<ApiEndpoint[]>([])
  const [adminOpen, setAdminOpen] = useState(false)

  useEffect(() => {
    ApiService.fetchApiEndpoints().then(setEndpoints)
  }, [])

  return (
    <aside
      className={`border-r border-white/40 dark:border-white/10 bg-white/40 dark:bg-zinc-900/40 backdrop-blur-2xl flex flex-col hidden md:flex shadow-xl shadow-slate-200/20 dark:shadow-none transition-all duration-500 ease-out overflow-hidden ${
        open ? 'w-64' : 'w-14'
      }`}
    >
      {/* Header */}
      <div
        className={`border-b border-white/40 dark:border-white/10 transition-opacity duration-500 ease-out ${
          open ? 'p-6 opacity-100' : 'p-2 opacity-0 h-0 overflow-hidden'
        }`}
      >
        <h1 className="text-xl font-bold tracking-tight whitespace-nowrap">
          Analisis Cuantitativo
        </h1>
        <p className="text-sm text-slate-500 dark:text-slate-400 mt-1 whitespace-nowrap">
          Modulo Isabelle
        </p>
      </div>

      <nav className="flex-1 overflow-y-auto p-3 space-y-6" aria-label="Navegacion principal">
        {/* Progress section */}
        <section
          className={`transition-all duration-500 ease-out ${
            open ? 'opacity-100 max-h-40' : 'opacity-0 max-h-0 overflow-hidden'
          }`}
        >
          <h3 className="text-xs font-semibold text-slate-400 uppercase tracking-wider mb-3 whitespace-nowrap">
            Progreso Actual
          </h3>
          <div className="space-y-2">
            <div className="flex justify-between text-sm whitespace-nowrap">
              <span>Revisados</span>
              <span className="font-medium">
                {reviewedCount} / {totalExercises}
              </span>
            </div>
            <div className="w-full bg-black/5 dark:bg-white/5 rounded-full h-2 shadow-inner border border-black/5 dark:border-white/5">
              <div
                className="bg-blue-500/90 h-2 rounded-full transition-all duration-700 ease-out shadow-[0_0_10px_rgba(59,130,246,0.5)]"
                style={{
                  width: totalExercises > 0
                    ? `${(reviewedCount / totalExercises) * 100}%`
                    : '0%',
                }}
                role="progressbar"
                aria-valuenow={reviewedCount}
                aria-valuemin={0}
                aria-valuemax={totalExercises}
              />
            </div>
          </div>
        </section>

        {/* Exercises section */}
        {open && (
          <section>
            <h3 className="text-xs font-semibold text-slate-400 uppercase tracking-wider mb-3 whitespace-nowrap">
              Ejercicios
            </h3>
            <ul className="space-y-1">
              {exercises.length === 0 && (
                <li className="px-3 py-2 text-sm text-slate-400 italic">
                  Sin ejercicios
                </li>
              )}

              {exercises.map((ex) => {
                const isActive = ex.id === currentExerciseId
                return (
                  <li key={ex.id}>
                    <button
                      onClick={() => onSelectExercise(ex.id)}
                      className={`w-full text-left px-3 py-2 text-sm rounded-lg transition-all duration-300 ease-out flex items-center gap-2 ${
                        isActive
                          ? 'bg-blue-500/10 border border-blue-500/30 text-blue-700 dark:text-blue-300'
                          : 'hover:bg-white/50 dark:hover:bg-white/5 hover:translate-x-1 border border-transparent'
                      }`}
                    >
                      <span
                        className={`w-2 h-2 rounded-full shrink-0 ${
                          ex.is_verified
                            ? 'bg-emerald-400 shadow-[0_0_8px_rgba(16,185,129,0.8)]'
                            : 'bg-slate-400 shadow-[0_0_8px_rgba(148,163,184,0.6)]'
                        }`}
                        title={ex.is_verified ? 'Verificado' : 'Pendiente'}
                      />
                      <span className="truncate">{ex.name}</span>
                    </button>
                  </li>
                )
              })}
            </ul>

            {hasMore && (
              <button
                onClick={onLoadMore}
                disabled={isLoadingMore}
                className="mt-2 w-full flex items-center justify-center gap-2 px-3 py-2 text-xs font-semibold rounded-lg text-slate-500 dark:text-slate-400 hover:bg-white/50 dark:hover:bg-white/5 disabled:opacity-50 transition-all duration-300 ease-out"
              >
                {isLoadingMore && <Loader2 className="w-3.5 h-3.5 animate-spin" />}
                {isLoadingMore ? 'Cargando...' : 'Cargar mas'}
              </button>
            )}
          </section>
        )}

        {/* Admin section */}
        <section>
          <button
            onClick={() => setAdminOpen(!adminOpen)}
            className={`flex items-center gap-2 w-full text-xs font-semibold text-slate-400 uppercase tracking-wider mb-3 whitespace-nowrap transition-all duration-500 ease-out hover:text-slate-600 dark:hover:text-slate-300 ${
              open ? 'opacity-100' : 'opacity-0 h-0 overflow-hidden'
            }`}
          >
            <Terminal className="w-3.5 h-3.5" />
            Administrador
          </button>
          <ul
            className={`space-y-1 overflow-hidden transition-all duration-500 ease-out ${
              adminOpen && open ? 'max-h-96 opacity-100' : 'max-h-0 opacity-0'
            }`}
          >
            {endpoints.map((ep, i) => (
              <li
                key={i}
                title={ep.summary}
                onClick={() => window.open(
                  window.location.origin + ep.path,
                  '_blank'
                )}
                className="px-3 py-1.5 text-xs rounded-lg hover:bg-white/50 dark:hover:bg-white/5 transition-all duration-300 ease-out cursor-pointer flex items-center gap-2"
              >
                <span
                  className={`shrink-0 text-[10px] font-bold px-1.5 py-0.5 rounded ${
                    ep.method === 'GET'
                      ? 'bg-blue-500/15 text-blue-600 dark:text-blue-400'
                      : 'bg-emerald-500/15 text-emerald-600 dark:text-emerald-400'
                  }`}
                >
                  {ep.method}
                </span>
                <code className="text-slate-500 dark:text-slate-400 truncate font-mono">
                  {ep.path}
                </code>
              </li>
            ))}
          </ul>
        </section>
      </nav>
    </aside>
  )
}
