import { useState, useRef, useMemo } from 'react'

interface IsabelleEditorProps {
  code: string
  onChange: (value: string) => void
}

// Complete Isabelle symbol → Unicode mapping (from Isabelle etc/symbols)
const ISABELLE_SYMBOLS: Record<string, string> = {
  // Arrows
  longrightarrow: '\u27F6', longleftarrow: '\u27F5', Longrightarrow: '\u27F9', Longleftarrow: '\u27F8',
  longleftrightarrow: '\u27F7', Longleftrightarrow: '\u27FA', rightarrow: '\u2192', leftarrow: '\u2190',
  Rightarrow: '\u21D2', Leftarrow: '\u21D0', leftrightarrow: '\u2194', Leftrightarrow: '\u21D4',
  rightharpoonup: '\u21C0', leftharpoonup: '\u21BF', rightharpoondown: '\u21C1', leftharpoondown: '\u21BD',
  rightleftharpoons: '\u21CC', mapsto: '\u21A6',

  // Greek lowercase
  alpha: '\u03B1', beta: '\u03B2', gamma: '\u03B3', delta: '\u03B4', epsilon: '\u03B5',
  zeta: '\u03B6', eta: '\u03B7', theta: '\u03B8', iota: '\u03B9', kappa: '\u03BA',
  lambda: '\u03BB', mu: '\u03BC', nu: '\u03BD', xi: '\u03BE', pi: '\u03C0',
  rho: '\u03C1', sigma: '\u03C3', tau: '\u03C4', upsilon: '\u03C5', phi: '\u03C6',
  chi: '\u03C7', psi: '\u03C8', omega: '\u03C9',

  // Greek uppercase
  Gamma: '\u0393', Delta: '\u0394', Theta: '\u0398', Lambda: '\u039B', Xi: '\u039E',
  Pi: '\u03A0', Sigma: '\u03A3', Phi: '\u03A6', Psi: '\u03A8', Omega: '\u03A9',

  // Logic
  forall: '\u2200', exists: '\u2203', nexists: '\u2204', not: '\u00AC',
  and: '\u2227', or: '\u2228', equiv: '\u2261',

  // Relations
  'in': '\u2208', notin: '\u2209', subset: '\u2282', supset: '\u2283',
  subseteq: '\u2286', supseteq: '\u2287', noteq: '\u2260', le: '\u2264', ge: '\u2265',
  sim: '\u223C', cong: '\u2245', approx: '\u2248', simeq: '\u2243', asymp: '\u224D',
  doteq: '\u2250', propto: '\u221D', models: '\u22A8',

  // Operators
  union: '\u222A', inter: '\u2229', squnion: '\u2294', sqinter: '\u2293',
  times: '\u00D7', div: '\u00F7', bullet: '\u2219', circ: '\u2218',
  oplus: '\u2295', ominus: '\u2296', otimes: '\u2297', oslash: '\u2298', odot: '\u2299',

  // Misc math
  infty: '\u221E', partial: '\u2202', nabla: '\u2207', surd: '\u221A',
  integral: '\u222B', oint: '\u222E', angle: '\u2220', ell: '\u2113',
  therefore: '\u2234', because: '\u2235',
  box: '\u25A1', diamond: '\u25C7', star: '\u22C6',
  parallel: '\u2225', perp: '\u22A5', top: '\u22A4', bottom: '\u22A5',
  lbrakk: '\u27E6', rbrakk: '\u27E7', langle: '\u27E8', rangle: '\u27E9',
  lparr: '\u27E8', rparr: '\u27E9', less: '<', greater: '>',
  nothing: '\u2205', hole: '\u25A1',

  // Number sets
  aleph: '\u2135', beth: '\u2136', gimel: '\u2137', daleth: '\u2138',
  R: '\u211D', N: '\u2115', Q: '\u211A', Z: '\u2124', C: '\u2102',

  // Special
  degree: '\u00B0', dagger: '\u2020', ddagger: '\u2021',
  sectionsign: '\u00A7', P: '\u00B6', copyright: '\u00A9',
}

function decodeIsabelleSymbols(text: string): string {
  return text.replace(/\\<([a-zA-Z_0-9^]+)>/g, (match, name) => {
    return ISABELLE_SYMBOLS[name] ?? match
  })
}

export function IsabelleEditor({ code, onChange }: IsabelleEditorProps) {
  const [isFocused, setIsFocused] = useState(false)
  const highlightRef = useRef<HTMLPreElement>(null)

  const handleScroll = (e: React.UIEvent<HTMLTextAreaElement>) => {
    if (highlightRef.current) {
      highlightRef.current.scrollTop = e.currentTarget.scrollTop
      highlightRef.current.scrollLeft = e.currentTarget.scrollLeft
    }
  }

  const highlightedCode = useMemo(() => {
    // Step 1: Convert Isabelle symbols to Unicode in the original code
    const decoded = decodeIsabelleSymbols(code)

    // Step 2: HTML escape
    let html = decoded
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')

    // Step 3: Syntax highlighting
    const regex =
      /("([^"\\]*(\\.[^"\\]*)*)")|(\(\*[\s\S]*?\*\))|\b(theory|imports|begin|end|lemma|theorem|proof|qed|apply|done|assumes|shows|by|auto|sorry|have|show|fix|assume)\b/g

    html = html.replace(
      regex,
      (match, strGrp, _inner1, _inner2, commentGrp, keywordGrp) => {
        if (strGrp)
          return `<span class="text-green-600 dark:text-green-400">${strGrp}</span>`
        if (commentGrp)
          return `<span class="text-gray-500 italic">${commentGrp}</span>`
        if (keywordGrp)
          return `<span class="text-blue-600 dark:text-blue-400 font-bold">${keywordGrp}</span>`
        return match
      }
    )

    if (html.endsWith('\n')) {
      html += ' '
    }

    return html
  }, [code])

  return (
    <div
      className={`relative w-full h-96 rounded-2xl border transition-all duration-500 ease-out bg-white/50 dark:bg-zinc-900/50 backdrop-blur-xl overflow-hidden shadow-inner ${
        isFocused
          ? 'border-blue-400/60 ring-4 ring-blue-500/10 dark:ring-blue-500/20 scale-[1.005]'
          : 'border-white/60 dark:border-white/10'
      }`}
    >
      <pre
        ref={highlightRef}
        className="absolute inset-0 p-4 m-0 font-mono text-sm leading-6 tracking-normal whitespace-pre-wrap break-words pointer-events-none text-gray-800 dark:text-gray-200 overflow-hidden"
        aria-hidden="true"
      >
        <code dangerouslySetInnerHTML={{ __html: highlightedCode }} />
      </pre>
      <textarea
        value={code}
        onChange={e => onChange(e.target.value)}
        onScroll={handleScroll}
        onFocus={() => setIsFocused(true)}
        onBlur={() => setIsFocused(false)}
        className="absolute inset-0 w-full h-full p-4 m-0 font-mono text-sm leading-6 tracking-normal whitespace-pre-wrap break-words bg-transparent resize-none text-transparent caret-black dark:caret-white outline-none"
        spellCheck="false"
        aria-label="Isabelle Code Editor"
      />
    </div>
  )
}
