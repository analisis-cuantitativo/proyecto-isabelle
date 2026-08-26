import { useCallback, useEffect, useState } from 'react'

const AUTH_STORAGE_KEY = 'auth_credentials'

function readStoredToken(): string | null {
  try {
    return localStorage.getItem(AUTH_STORAGE_KEY)
  } catch {
    return null
  }
}

export function useAuth() {
  const [token, setToken] = useState<string | null>(readStoredToken)

  const login = useCallback(
    async (username: string, password: string): Promise<string | null> => {
      const candidate = btoa(`${username}:${password}`)
      try {
        const res = await fetch('/api/auth/login', {
          headers: { Authorization: `Basic ${candidate}` },
        })
        if (!res.ok) {
          return 'Usuario o contrasena incorrectos'
        }
      } catch {
        return 'Error de conexion con el servidor'
      }

      try {
        localStorage.setItem(AUTH_STORAGE_KEY, candidate)
      } catch {
        // ignore storage errors
      }
      setToken(candidate)
      return null
    },
    []
  )

  const logout = useCallback(() => {
    try {
      localStorage.removeItem(AUTH_STORAGE_KEY)
    } catch {
      // ignore storage errors
    }
    setToken(null)
  }, [])

  useEffect(() => {
    window.addEventListener('auth:unauthorized', logout)
    return () => window.removeEventListener('auth:unauthorized', logout)
  }, [logout])

  return {
    isAuthenticated: token !== null,
    logout,
    login,
  }
}
