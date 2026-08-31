import { useState, type FormEvent } from 'react'
import { Lock } from 'lucide-react'

interface LoginProps {
  onLogin: (username: string, password: string) => Promise<string | null>
}

export function Login({ onLogin }: LoginProps) {
  const [username, setUsername] = useState('')
  const [password, setPassword] = useState('')
  const [error, setError] = useState<string | null>(null)
  const [isSubmitting, setIsSubmitting] = useState(false)

  const handleSubmit = async (e: FormEvent) => {
    e.preventDefault()
    setIsSubmitting(true)
    setError(null)
    const result = await onLogin(username, password)
    if (result) setError(result)
    setIsSubmitting(false)
  }

  return (
    <div className="flex h-screen items-center justify-center bg-slate-50 dark:bg-zinc-950 text-slate-900 dark:text-slate-100 px-4">
      <form
        onSubmit={handleSubmit}
        className="w-full max-w-sm space-y-6 bg-white/60 dark:bg-zinc-900/60 backdrop-blur-xl rounded-2xl p-8 border border-white/60 dark:border-white/10 shadow-xl"
      >
        <div className="flex flex-col items-center gap-2 text-center">
          <div className="w-12 h-12 bg-blue-500/10 border border-blue-500/20 rounded-full flex items-center justify-center">
            <Lock className="w-5 h-5 text-blue-600 dark:text-blue-400" />
          </div>
          <h1 className="text-xl font-bold tracking-tight">Iniciar sesion</h1>
          <p className="text-sm text-slate-500 dark:text-slate-400">
            Ingresa tus credenciales para continuar
          </p>
        </div>

        <div className="space-y-3">
          <input
            type="text"
            autoFocus
            autoComplete="username"
            placeholder="Usuario"
            value={username}
            onChange={e => setUsername(e.target.value)}
            className="w-full px-4 py-2.5 rounded-xl bg-white/70 dark:bg-zinc-800/70 border border-white/60 dark:border-white/10 outline-none focus:ring-2 focus:ring-blue-500/40 transition-all duration-300"
          />
          <input
            type="password"
            autoComplete="current-password"
            placeholder="Contrasena"
            value={password}
            onChange={e => setPassword(e.target.value)}
            className="w-full px-4 py-2.5 rounded-xl bg-white/70 dark:bg-zinc-800/70 border border-white/60 dark:border-white/10 outline-none focus:ring-2 focus:ring-blue-500/40 transition-all duration-300"
          />
        </div>

        {error && (
          <p className="text-sm text-rose-600 dark:text-rose-400 text-center">{error}</p>
        )}

        <button
          type="submit"
          disabled={isSubmitting || !username || !password}
          className="w-full px-4 py-2.5 bg-blue-500/10 text-blue-700 dark:text-blue-300 border border-blue-500/20 rounded-xl hover:bg-blue-500/20 disabled:opacity-50 transition-all duration-300 font-medium"
        >
          {isSubmitting ? 'Verificando...' : 'Entrar'}
        </button>
      </form>
    </div>
  )
}
