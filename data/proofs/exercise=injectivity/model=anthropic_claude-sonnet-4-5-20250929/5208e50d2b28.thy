theory InjectiveLeftInverse
  imports Main
begin

theorem injective_iff_left_inverse:
  fixes f :: "'a ⇒ 'b"
  shows "inj f ⟷ (∃g. ∀x. g (f x) = x)"
proof
  (* Forward direction: injective implies left inverse exists *)
  assume inj_f: "inj f"

  (* Define g using Hilbert's choice operator *)
  define g where "g = (λy. SOME x. f x = y)"

  (* Show that g is a left inverse of f *)
  have "∀x. g (f x) = x"
  proof
    fix x
    have "f (SOME x'. f x' = f x) = f x"
      by (rule someI[of "λx'. f x' = f x" x]) simp
    with inj_f have "(SOME x'. f x' = f x) = x"
      unfolding inj_def by auto
    thus "g (f x) = x"
      unfolding g_def by simp
  qed
  thus "∃g. ∀x. g (f x) = x" by blast
next
  (* Backward direction: left inverse exists implies injective *)
  assume "∃g. ∀x. g (f x) = x"
  then obtain g where g_left_inv: "∀x. g (f x) = x" by blast

  show "inj f"
    unfolding inj_def
  proof (intro allI impI)
    fix x y
    assume "f x = f y"
    hence "g (f x) = g (f y)" by simp
    with g_left_inv show "x = y" by simp
  qed
qed

end
