declare global {
  interface Window {
    katex: {
      renderToString: (math: string, options?: any) => string
    }
  }
}

export {}
