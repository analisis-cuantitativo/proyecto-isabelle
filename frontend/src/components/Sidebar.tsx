import { useEffect, useState } from 'react'
import { Terminal } from 'lucide-react'
import { ApiService } from '../services/api'
import type { CategoryResponse, ApiEndpoint } from '../types'

const CATEGORY_ICONS: Record<string, { color: string; dot: string }> = {
  'Logic Basics': { color: 'bg-blue-400', dot: 'shadow-[0_0_8px_rgba(59,130,246,0.8)]' },
  'Set Theory': { color: 'bg-purple-400', dot: 'shadow-[0_0_8px_rgba(168,85,247,0.8)]' },
  Induction: { color: 'bg-emerald-400', dot: 'shadow-[0_0_8px_rgba(16,185,129,0.8)]' },
  'Advanced Proofs': { color: 'bg-amber-400', dot: 'shadow-[0_0_8px_rgba(251,191,36,0.8)]' },
}

const FALLBACK_COLOR = 'bg-slate-400'
const FALLBACK_DOT = 'shadow-[0_0_8px_rgba(148,163,184,0.8)]'

interface SidebarProps {
  open: boolean
  categories: CategoryResponse[]
  reviewedCount: number
  totalExercises: number
  hasVerified: boolean
}

export function Sidebar({
  open,
  categories,
  reviewedCount,
  totalExercises,
  hasVerified,
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

        {/* Topics section */}
        <section>
          <h3
            className={`text-xs font-semibold text-slate-400 uppercase tracking-wider mb-3 whitespace-nowrap transition-all duration-500 ease-out ${
              open ? 'opacity-100' : 'opacity-0 h-0 overflow-hidden'
            }`}
          >
            Topicos
          </h3>
          <ul className="space-y-1">
            {categories.length === 0 && open && (
              <li className="px-3 py-2 text-sm text-slate-400 italic">
                Sin topicos
              </li>
            )}

            {hasVerified && open && (
              <li className="px-3 py-2">
                <div className="relative">
                  <div className="h-px w-full bg-gradient-to-r from-transparent via-slate-300/70 to-transparent dark:via-slate-600/50" />
                  <span className="absolute -top-2 left-1/2 -translate-x-1/2 px-2 text-[10px] font-bold tracking-widest uppercase text-slate-400 bg-slate-50 dark:bg-zinc-950">
                    Revisados
                  </span>
                </div>
              </li>
            )}

            {categories.map((cat) => {
              const icon = CATEGORY_ICONS[cat.name] ?? {
                color: FALLBACK_COLOR,
                dot: FALLBACK_DOT,
              }
              return open ? (
                <li
                  key={cat.name}
                  className="px-3 py-2 text-sm rounded-lg hover:bg-white/50 dark:hover:bg-white/5 transition-all duration-300 ease-out cursor-pointer flex items-center justify-between hover:translate-x-1"
                >
                  <span className="flex items-center gap-2">
                    <span
                      className={`w-2 h-2 rounded-full ${icon.color} ${icon.dot}`}
                    />
                    {cat.name}
                  </span>
                  <span className="text-xs text-slate-400 bg-black/5 dark:bg-white/10 px-2 py-0.5 rounded-full">
                    {cat.exercise_count}
                  </span>
                </li>
              ) : (
                <li
                  key={cat.name}
                  title={`${cat.name} (${cat.exercise_count})`}
                  className="flex items-center justify-center py-2 cursor-pointer hover:bg-white/40 dark:hover:bg-white/5 rounded-lg transition-all duration-300 ease-out"
                >
                  <span
                    className={`w-3 h-3 rounded-full ${icon.color} ${icon.dot} transition-transform duration-300 ease-out hover:scale-125`}
                  />
                </li>
              )
            })}
          </ul>
        </section>

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
