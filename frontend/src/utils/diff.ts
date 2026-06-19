import type { DiffLine } from '../types'

export function generatePatch(oldCode = '', newCode = ''): DiffLine[] {
  const oldLines = (oldCode || '').split('\n')
  const newLines = (newCode || '').split('\n')
  const patch: DiffLine[] = []

  let i = 0, j = 0
  while (i < oldLines.length || j < newLines.length) {
    if (i < oldLines.length && j < newLines.length && oldLines[i] === newLines[j]) {
      i++; j++
    } else {
      let resynced = false
      for (let k = 1; k < 6; k++) {
        if (i + k < oldLines.length && oldLines[i + k] === newLines[j]) {
          for (let l = 0; l < k; l++) patch.push({ type: 'removed', text: oldLines[i++] })
          resynced = true; break
        }
        if (j + k < newLines.length && oldLines[i] === newLines[j + k]) {
          for (let l = 0; l < k; l++) patch.push({ type: 'added', text: newLines[j++] })
          resynced = true; break
        }
      }
      if (!resynced) {
        if (i < oldLines.length) patch.push({ type: 'removed', text: oldLines[i++] })
        if (j < newLines.length) patch.push({ type: 'added', text: newLines[j++] })
      }
    }
  }
  return patch
}
