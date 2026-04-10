theory InjectiveLeftInverse
  imports Main
begin

lemma injective_iff_left_inverse:
  fixes f :: "'a ⇒ 'b"
  shows "inj f ⟷ (∃g :: 'b ⇒ 'a. ∀x. g (f x) = x)"
proof
  assume "inj f"
  then show "∃g :: 'b ⇒ 'a. ∀x. g (f x) = x"
  proof (cases "∃x::'a. True")
    case True
    then obtain a0 :: 'a where "True" by blast
    define g :: "'b ⇒ 'a" where
      "g = (λy. if y ∈ range f then (THE x. f x = y) else a0)"
    have "∀x. g (f x) = x"
    proof
      fix x
      have "f x ∈ range f" by simp
      then have "g (f x) = (THE z. f z = f x)"
        unfolding g_def by simp
      also have "... = x"
      proof (rule the_equality)
        show "f x = f x" by simp
      next
        fix z assume "f z = f x"
        with ‹inj f› show "z = x"
          unfolding inj_def by blast
      qed
      finally show "g (f x) = x" .
    qed
    then show ?thesis by blast
  next
    case False
    then show ?thesis by blast
  qed
next
  assume "∃g :: 'b ⇒ 'a. ∀x. g (f x) = x"
  then obtain g :: "'b ⇒ 'a" where g_prop: "∀x. g (f x) = x" by blast
  show "inj f"
    unfolding inj_def
  proof (intro allI impI)
    fix x y
    assume "f x = f y"
    then have "g (f x) = g (f y)" by simp
    with g_prop show "x = y" by simp
  qed
qed

end
