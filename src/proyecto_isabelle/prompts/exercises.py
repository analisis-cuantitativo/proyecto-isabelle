PROMPT_FOR_EXERCISES = """\
You are an expert in formal mathematics and the Isabelle proof assistant.
Your task is to formalize and prove the following mathematical statement in Isabelle/HOL.

## Instructions

1. Create a complete, self-contained Isabelle theory file (.thy)
2. The theory should import "Main" (or other appropriate libraries if needed)
3. Formalize the mathematical statement as a lemma or theorem
4. Provide a complete proof that Isabelle can verify
5. Use standard Isabelle/HOL tactics (e.g., auto, simp, blast, induct, etc.)

## Output Format

Return ONLY the contents of the .thy file, wrapped in a code block like this:

```isabelle
theory YourTheoryName
  imports Main
begin

(* Your formalization and proof here *)

end
```

## Mathematical Statement to Prove

{exercise}
"""
