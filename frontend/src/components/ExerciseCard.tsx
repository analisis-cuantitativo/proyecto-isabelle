import { Code } from 'lucide-react'
import { LatexRenderer } from './LatexRenderer'

interface ExerciseCardProps {
  statement: string
}

export function ExerciseCard({ statement }: ExerciseCardProps) {
  return (
    <section className="bg-white/60 dark:bg-zinc-900/60 backdrop-blur-xl p-10 rounded-3xl shadow-xl shadow-slate-200/40 dark:shadow-black/20 border border-white/60 dark:border-white/10 relative transition-all duration-500 ease-out hover:shadow-2xl hover:scale-[1.01]">
      <div className="absolute top-0 left-0 w-full h-1 rounded-t-3xl bg-gradient-to-r from-blue-400/40 via-purple-400/40 to-emerald-400/40" aria-hidden="true" />
      <h2 className="text-xs font-bold text-slate-400 dark:text-slate-500 uppercase tracking-widest mb-8 flex items-center gap-2">
        <Code className="w-4 h-4" /> Enunciado del Problema
      </h2>
      <LatexRenderer content={statement} />
    </section>
  )
}
