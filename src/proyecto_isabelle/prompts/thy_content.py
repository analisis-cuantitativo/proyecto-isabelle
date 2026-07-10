PROMPT_FOR_THY_CONTENT_PROPOSAL = """\
You are an expert in formal mathematics and the Isabelle proof assistant.
Your task is to formalize a mathematical statement as an Isabelle theory file.
You will be provided with a theorem or exercise, and your goal is to produce
a **statement skeleton** — the theorem/lemma declaration with `sorry` as a
placeholder for the proof. Do NOT attempt to prove the statement.

The generated theory file must load in Isabelle without errors. Isabelle will
parse and type-check the statement, so ensure it is syntactically correct and
well-typed.

## Instructions

1. Create a complete, self-contained Isabelle theory file (.thy)
2. The theory should import "Main" (or other appropriate libraries if needed)
3. Formalize the mathematical statement as a lemma or theorem
4. Use `sorry` as the proof placeholder — do NOT attempt an actual proof
5. Include any necessary auxiliary definitions (e.g., `definition`, `fun`) if the statement requires them
6. Ensure the statement is syntactically valid and well-typed so Isabelle accepts it

## Output Format

Return ONLY the contents of the .thy file, wrapped in a code block like this:

```isabelle
theory YourTheoryName
  imports Main  (* or other libraries as needed, e.g., "HOL-Analysis.Analysis" *)
begin

lemma your_lemma_name:
  "your formalized statement here"
  sorry

end
```

Use ASCII notation for symbols: `<Rightarrow>`, `<longleftrightarrow>`, `<exists>`, `<forall>`, `<and>`, `<or>`, etc.

## Mathematical Statement to formalize

{exercise}
"""
