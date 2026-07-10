import { Moon, Sun, PanelLeftOpen, PanelLeftClose } from 'lucide-react'

interface HeaderProps {
  theme: 'dark' | 'light'
  onToggleTheme: () => void
  title: string | undefined
  topic: string | undefined
  sidebarOpen: boolean
  onToggleSidebar: () => void
}

export function Header({
  theme,
  onToggleTheme,
  title,
  topic,
  sidebarOpen,
  onToggleSidebar,
}: HeaderProps) {
  return (
    <header className="h-16 border-b border-white/40 dark:border-white/10 flex items-center justify-between px-6 bg-white/40 dark:bg-zinc-900/40 backdrop-blur-2xl z-10 shadow-sm">
      <div className="flex items-center gap-3">
        <button
          onClick={onToggleSidebar}
          className="p-2 rounded-xl bg-white/40 dark:bg-zinc-800/40 hover:bg-white/80 dark:hover:bg-zinc-700/80 border border-white/50 dark:border-white/10 transition-all duration-500 ease-out shadow-sm"
          aria-label={sidebarOpen ? 'Colapsar barra lateral' : 'Expandir barra lateral'}
        >
          {sidebarOpen ? (
            <PanelLeftClose className="w-4 h-4 text-slate-500" />
          ) : (
            <PanelLeftOpen className="w-4 h-4 text-slate-500" />
          )}
        </button>

        <span className="bg-blue-500/10 text-blue-700 dark:bg-blue-500/20 dark:text-blue-300 border border-blue-500/20 text-xs font-semibold px-3 py-1 rounded-full shadow-sm">
          {topic || '-'}
        </span>
        <span className="text-sm font-medium text-slate-600 dark:text-slate-300 truncate max-w-[50vw]">
          {title || 'Completado'}
        </span>
      </div>

      <div className="flex items-center gap-4">
        <button
          onClick={onToggleTheme}
          className="p-2 rounded-full bg-white/40 dark:bg-zinc-800/40 hover:bg-white/80 dark:hover:bg-zinc-700/80 border border-white/50 dark:border-white/10 transition-all duration-500 ease-out shadow-sm group"
          aria-label={theme === 'dark' ? 'Activar modo claro' : 'Activar modo oscuro'}
        >
          {theme === 'dark' ? (
            <Sun className="w-4 h-4 group-hover:rotate-90 transition-transform duration-500 ease-out" />
          ) : (
            <Moon className="w-4 h-4 group-hover:-rotate-12 transition-transform duration-500 ease-out" />
          )}
        </button>
      </div>
    </header>
  )
}
