import { useEffect, type RefObject } from 'react'

type ActionHandler = {
  onApprove: () => void
  onReject: () => void
  onSkip: () => void
  onPrevious: () => void
  onUndo: () => void
}

export function useKeyboardShortcuts(
  handlers: ActionHandler,
  enabled = true,
  editorRef?: RefObject<HTMLTextAreaElement | null>
) {
  useEffect(() => {
    if (!enabled) return

    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.target instanceof HTMLTextAreaElement) return

      switch (e.key) {
        case 'ArrowRight':
          e.preventDefault()
          handlers.onApprove()
          break
        case 'ArrowLeft':
          e.preventDefault()
          handlers.onReject()
          break
        case 'ArrowUp':
          e.preventDefault()
          handlers.onUndo()
          break
        case 's':
        case 'ArrowDown':
          e.preventDefault()
          handlers.onSkip()
          break
        case 'w':
          e.preventDefault()
          handlers.onPrevious()
          break
      }
    }

    window.addEventListener('keydown', handleKeyDown)
    return () => window.removeEventListener('keydown', handleKeyDown)
  }, [handlers, enabled])
}
