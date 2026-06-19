import type { HistoryEntry } from '../types'

interface HistoryPanelProps {
  history: HistoryEntry[]
}

export function HistoryPanel({ history }: HistoryPanelProps) {
  if (history.length === 0) {
    return (
      <p className="text-sm text-slate-400 italic">
        No hay modificaciones registradas.
      </p>
    )
  }

  return (
    <div className="space-y-4">
      {history.map((patch, idx) => (
        <div
          key={idx}
          className="p-4 bg-white/40 dark:bg-black/20 backdrop-blur-md rounded-xl border border-white/50 dark:border-white/5 text-xs font-mono overflow-x-auto shadow-sm hover:scale-[1.02] transition-all duration-300 ease-out"
        >
          <div className="flex justify-between items-center text-slate-400 mb-3 font-sans border-b border-black/5 dark:border-white/5 pb-2">
            <span>{patch.time}</span>
            <span
              className={`px-2 py-1 rounded-md text-[10px] uppercase font-bold tracking-wider ${
                patch.decision === 'approved'
                  ? 'bg-emerald-500/20 text-emerald-700 dark:text-emerald-400'
                  : 'bg-rose-500/20 text-rose-700 dark:text-rose-400'
              }`}
            >
              {patch.decision === 'approved' ? 'Aprobado' : 'Rechazado'}
            </span>
          </div>
          <div className="space-y-1">
            {patch.diff.map((line, lIdx) => (
              <div
                key={lIdx}
                className={`whitespace-pre rounded px-2 py-1 ${
                  line.type === 'added'
                    ? 'text-emerald-700 dark:text-emerald-300 bg-emerald-500/10'
                    : 'text-rose-700 dark:text-rose-300 bg-rose-500/10 line-through opacity-80'
                }`}
              >
                {line.type === 'added' ? '+ ' : '- '}
                {line.text}
              </div>
            ))}
          </div>
        </div>
      ))}
    </div>
  )
}
