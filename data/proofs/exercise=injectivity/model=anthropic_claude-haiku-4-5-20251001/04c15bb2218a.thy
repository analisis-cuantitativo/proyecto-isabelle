theory FunctionInjectivity
  imports Main
begin

theorem injective_iff_left_inverse (f : 'a → 'b) :
  "inj f ↔ (∃g : 'b → 'a. (g ∘ f) = id)" by
  constructor
  · intro h
    obtain x0 : 'a from UNIV_nonempty.ex
    let g : 'b → 'a := fun b => if ∃a. f a = b then (SOME a. f a = b) else x0
    use g
    ext a
    simp only [Function.comp_apply]
    show g (f a) = a
    simp only [g]
    split
    · rename_i ⟨a', ha'⟩
      have : f a = f a' := ha'
      exact h this
    · exfalso
      apply absurd
      exact ⟨a, rfl⟩
  · intro ⟨g, hg⟩
    intro a a' hab
    have eq1 : g (f a) = a := by rw [Function.comp_apply] at hg; simp only [id] at hg; rw [hg]
    have eq2 : g (f a') = a' := by rw [Function.comp_apply] at hg; simp only [id] at hg; rw [hg]
    rw [hab] at eq1
    exact eq1.trans eq2.symm

end
