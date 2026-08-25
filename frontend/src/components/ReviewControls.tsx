import { Check, X, Undo2, SkipForward, SkipBack, ShieldCheck, Loader2 } from 'lucide-react'

interface ReviewControlsProps {
  onApprove: () => void
  onReject: () => void
  onSkip: () => void
  onPrevious: () => void
  onUndo: () => void
  onVerify: () => void
  canUndo: boolean
  canSkip: boolean
  canPrevious: boolean
  approveEnabled: boolean
  isVerifying: boolean
}

export function ReviewControls({
  onApprove,
  onReject,
  onSkip,
  onPrevious,
  onUndo,
  onVerify,
  canUndo,
  canSkip,
  canPrevious,
  approveEnabled,
  isVerifying,
}: ReviewControlsProps) {
  return (
    <div className="flex flex-col items-center gap-4 mt-6">
      <button
        onClick={onVerify}
        disabled={isVerifying}
        className="flex items-center gap-2 px-5 py-2.5 text-sm font-semibold rounded-xl bg-blue-500/10 text-blue-700 dark:text-blue-300 border border-blue-500/20 hover:bg-blue-500/20 active:scale-95 disabled:opacity-50 disabled:cursor-not-allowed transition-all duration-500 ease-out shadow-sm"
      >
        {isVerifying ? (
          <Loader2 className="w-4 h-4 animate-spin" />
        ) : (
          <ShieldCheck className="w-4 h-4" />
        )}
        {isVerifying ? 'Verificando...' : 'Verificar con DeepIsaHOL'}
      </button>

      <section className="flex items-center justify-center gap-4" aria-label="Controles de decision">
        <button
          onClick={onReject}
          className="group relative flex flex-col items-center justify-center w-20 h-20 bg-white/60 dark:bg-zinc-800/60 backdrop-blur-xl border border-white/60 dark:border-white/10 rounded-full hover:border-rose-400/50 hover:bg-rose-50/80 dark:hover:bg-rose-900/20 active:scale-95 transition-all duration-500 ease-out shadow-xl shadow-slate-200/50 dark:shadow-black/30 hover:shadow-rose-500/20"
          aria-label="Rechazar ejercicio"
        >
          <X className="w-9 h-9 text-rose-500 group-hover:scale-110 transition-transform duration-500 ease-out" />
          <span className="absolute -bottom-8 text-xs font-bold text-slate-400 opacity-0 group-hover:opacity-100 transition-opacity duration-500 ease-out whitespace-nowrap tracking-widest uppercase">
            Rechazar (&larr;)
          </span>
        </button>

        <button
          onClick={onPrevious}
          disabled={!canPrevious}
          className="group relative flex items-center justify-center w-12 h-12 bg-white/40 dark:bg-zinc-800/40 backdrop-blur-md border border-white/50 dark:border-white/10 rounded-full hover:bg-white/80 dark:hover:bg-zinc-700/80 active:scale-90 disabled:opacity-30 disabled:cursor-not-allowed transition-all duration-500 ease-out shadow-md"
          aria-label="Ejercicio anterior"
        >
          <SkipBack className="w-5 h-5 text-slate-500 group-hover:-translate-x-0.5 transition-transform duration-500 ease-out" />
        </button>

        <button
          onClick={onUndo}
          disabled={!canUndo}
          className="group relative flex items-center justify-center w-12 h-12 bg-white/40 dark:bg-zinc-800/40 backdrop-blur-md border border-white/50 dark:border-white/10 rounded-full hover:bg-white/80 dark:hover:bg-zinc-700/80 active:scale-90 disabled:opacity-30 disabled:cursor-not-allowed transition-all duration-500 ease-out shadow-md"
          aria-label="Deshacer decision anterior"
        >
          <Undo2 className="w-5 h-5 text-slate-500 group-hover:-rotate-45 transition-transform duration-500 ease-out" />
        </button>

        <button
          onClick={onSkip}
          disabled={!canSkip}
          className="group relative flex items-center justify-center w-12 h-12 bg-white/40 dark:bg-zinc-800/40 backdrop-blur-md border border-white/50 dark:border-white/10 rounded-full hover:bg-white/80 dark:hover:bg-zinc-700/80 active:scale-90 disabled:opacity-30 disabled:cursor-not-allowed transition-all duration-500 ease-out shadow-md"
          aria-label="Saltar ejercicio"
        >
          <SkipForward className="w-5 h-5 text-slate-500 group-hover:translate-x-0.5 transition-transform duration-500 ease-out" />
        </button>

        <button
          onClick={onApprove}
          disabled={!approveEnabled}
          title={approveEnabled ? undefined : 'Verifica el codigo con DeepIsaHOL antes de aprobar'}
          className="group relative flex flex-col items-center justify-center w-20 h-20 bg-white/60 dark:bg-zinc-800/60 backdrop-blur-xl border border-white/60 dark:border-white/10 rounded-full hover:border-emerald-400/50 hover:bg-emerald-50/80 dark:hover:bg-emerald-900/20 active:scale-95 disabled:opacity-30 disabled:cursor-not-allowed disabled:hover:border-white/60 disabled:hover:bg-white/60 dark:disabled:hover:bg-zinc-800/60 transition-all duration-500 ease-out shadow-xl shadow-slate-200/50 dark:shadow-black/30 hover:shadow-emerald-500/20"
          aria-label="Aprobar ejercicio"
        >
          <Check className="w-9 h-9 text-emerald-500 group-hover:scale-110 transition-transform duration-500 ease-out" />
          <span className="absolute -bottom-8 text-xs font-bold text-slate-400 opacity-0 group-hover:opacity-100 transition-opacity duration-500 ease-out whitespace-nowrap tracking-widest uppercase">
            Aprobar (&rarr;)
          </span>
        </button>
      </section>
    </div>
  )
}
