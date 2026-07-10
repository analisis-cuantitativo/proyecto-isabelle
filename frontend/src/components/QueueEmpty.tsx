import { Check, Undo2 } from 'lucide-react'

interface QueueEmptyProps {
  canUndo: boolean
  onUndo: () => void
}

export function QueueEmpty({ canUndo, onUndo }: QueueEmptyProps) {
  return (
    <div className="flex flex-col items-center justify-center h-full text-center space-y-4 animate-fade-in">
      <div className="w-24 h-24 bg-emerald-500/10 border border-emerald-500/20 rounded-full flex items-center justify-center mb-4 shadow-[0_0_30px_rgba(16,185,129,0.2)] animate-pulse-slow">
        <Check className="w-12 h-12 text-emerald-600 dark:text-emerald-400" />
      </div>
      <h2 className="text-3xl font-bold tracking-tight">Verificacion completada</h2>
      <p className="text-slate-500 dark:text-slate-400">
        Has procesado toda la cola de validaciones actual.
      </p>
      <button
        onClick={onUndo}
        disabled={!canUndo}
        className="mt-8 flex items-center gap-2 px-6 py-3 bg-white/60 dark:bg-zinc-800/60 backdrop-blur-md rounded-xl hover:bg-white/90 dark:hover:bg-zinc-700/90 border border-white/60 dark:border-white/10 disabled:opacity-50 transition-all duration-500 ease-out shadow-sm hover:shadow-md"
      >
        <Undo2 className="w-4 h-4" />
        Deshacer ultima revision
      </button>
    </div>
  )
}
