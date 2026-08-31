import { useState, useEffect, useRef } from 'react'

interface LatexRendererProps {
  content: string
}

export function LatexRenderer({ content }: LatexRendererProps) {
  const containerRef = useRef<HTMLDivElement>(null)
  const [isLoaded, setIsLoaded] = useState(typeof window.katex !== 'undefined')

  useEffect(() => {
    if (!isLoaded) {
      const script = document.createElement('script')
      script.src = 'https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/katex.min.js'
      script.onload = () => setIsLoaded(true)
      document.head.appendChild(script)

      const link = document.createElement('link')
      link.rel = 'stylesheet'
      link.href = 'https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/katex.min.css'
      document.head.appendChild(link)
    }
  }, [isLoaded])

  useEffect(() => {
    if (isLoaded && containerRef.current && window.katex) {
      const normalizeIsabelleLatex = (s: string) => {
        // Isabelle prints some tokens as \<Token>. KaTeX expects standard LaTeX commands.
        return (s || '')
          .replace(/\\<Longrightarrow>/g, '\\Longrightarrow')
          .replace(/\\<Rightarrow>/g, '\\Rightarrow')
          .replace(/\\<rightarrow>/g, '\\rightarrow')
          .replace(/\\<forall>/g, '\\forall')
          .replace(/\\<exists>/g, '\\exists')
          .replace(/\\<not>/g, '\\neg')
          .replace(/\\<or>/g, '\\lor')
          .replace(/\\<and>/g, '\\land')
          .replace(/\\<in>/g, '\\in')
          .replace(/\\<subseteq>/g, '\\subseteq')
          .replace(/\\<union>/g, '\\cup')
          .replace(/\\<inter>/g, '\\cap')
      }

      let htmlContent = content.replace(/\$\$([\s\S]*?)\$\$/g, (_match, math) => {
        try {
          return window.katex.renderToString(normalizeIsabelleLatex(math), { displayMode: true })
        } catch (_e) {
          return _match
        }
      })
      htmlContent = htmlContent.replace(/\$([^$]+)\$/g, (_match, math) => {
        try {
          return window.katex.renderToString(normalizeIsabelleLatex(math), { displayMode: false })
        } catch (_e) {
          return _match
        }
      })
      containerRef.current.innerHTML = htmlContent
    }
  }, [content, isLoaded])

  return <div ref={containerRef} className="text-lg md:text-xl font-serif leading-loose" />
}
