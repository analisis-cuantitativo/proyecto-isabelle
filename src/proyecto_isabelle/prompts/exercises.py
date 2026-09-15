import re

PROMPT_FOR_EXERCISES = """\
You are an expert in formal mathematics and the Isabelle proof assistant.
Your task is to formalize and prove the following mathematical statement in Isabelle/HOL.

## Instructions

1. Create a complete, self-contained Isabelle theory file (.thy)
2. Import "Main", plus any of the libraries listed below that the proof needs
3. Formalize the mathematical statement as a lemma or theorem
4. Provide a complete proof that Isabelle can verify
5. Use standard Isabelle/HOL tactics (e.g., auto, simp, blast, induct, etc.)
6. Do NOT use `sorry` or `oops` — a proof containing either counts as failed

## Available libraries

The theory is checked with `isabelle build` against a heap that has the Isabelle
distribution libraries prebuilt, so `imports` are honoured with no build wait.
`imports Main` alone is fine; add any of these (import only what you use):

- `Complex_Main` — real & complex numbers, limits, series, derivatives, transcendental functions
- `"HOL-Analysis.Analysis"` — topology, metric spaces, measure theory, integration, multivariate & complex analysis
- `"HOL-Probability.Probability"` — probability spaces, PMFs, expectation/variance, independence, distributions
- `"HOL-Number_Theory.Number_Theory"` — congruences, Fermat/Euler, totient, quadratic reciprocity
- `"HOL-Computational_Algebra.Computational_Algebra"` — polynomials, primes & factorization, formal power series
- `"HOL-Algebra.Algebra"` — groups, rings, fields, ideals, quotient structures (locale/record based)
- `"HOL-Combinatorics.Combinatorics"` — permutations, cycles, Stirling numbers
- `"HOL-Cardinals.Cardinals"` — ordinals and cardinal arithmetic
- proof methods: `"HOL-Eisbach.Eisbach"`, `"HOL-Decision_Procs.Approximation"` (`approximation`), `"HOL-Real_Asymp.Real_Asymp"` (`real_asymp`), `"HOL-Library.Sum_of_Squares"` (`sos`)
- individual `"HOL-Library.*"` theories (e.g. `Multiset`, `FSet`, `Extended_Real`)

## Output Format

Return ONLY the contents of the .thy file, wrapped in a code block like this:

```isabelle
theory YourTheoryName
  imports Main
begin

(* Your formalization and proof here *)

end
```

We recommend you use e.g. `<Rightarrow>` or `<longleftrightarrow>` or `<exists>` instead of the unicode alternatives.

## Mathematical Statement to Prove

{exercise}
"""

PROMPT_FOR_EXERCISES_WITH_PROOF = (
    PROMPT_FOR_EXERCISES
    + """

## Proof of that statement in natural language

{proof}
"""
)

PROMPT_FOR_EXERCISES_WITH_PROOF_AND_ERRORS = (
    PROMPT_FOR_EXERCISES_WITH_PROOF
    + """

## Previous attempts:

{previous_attempts}

"""
)


def extract_thy_content(response: str) -> str | None:
    """Extract the .thy file content from an LLM response.

    Looks for code blocks marked with ```isabelle or ``` and extracts the content.
    """
    pattern = r"```(?:isabelle|thy)?\s*\n(.*?)\n```"
    match = re.search(pattern, response, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None
