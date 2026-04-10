theory InjectiveLeftInverse
  imports Main
begin

theorem injective_iff_left_inverse:
  fixes f :: "'a ⇒ 'b"
  shows "inj f ⟷ (∃g :: 'b ⇒ 'a. g ∘ f = id)"
proof
  (* Forward direction: injective implies left inverse exists *)
  assume inj_f: "inj f"
  (* Construct g using Hilbert choice operator *)
  define g where "g = (λy. SOME x. f x = y)"
  have "g ∘ f = id"
  proof (rule ext)
    fix x
    have "(g ∘ f) x = (SOME z. f z = f x)"
      unfolding g_def by simp
    also have "... = x"
    proof (rule some_equality)
      show "f x = f x" by simp
    next
      fix z assume "f z = f x"
      with inj_f show "z = x"
        unfolding inj_def by simp
    qed
    finally show "(g ∘ f) x = id x" by simp
  qed
  thus "∃g :: 'b ⇒ 'a. g ∘ f = id" ..
next
  (* Backward direction: left inverse exists implies injective *)
  assume "∃g :: 'b ⇒ 'a. g ∘ f = id"
  then obtain g where gf_id: "g ∘ f = id" ..
  show "inj f"
    unfolding inj_def
  proof (intro allI impI)
    fix x y
    assume "f x = f y"
    hence "g (f x) = g (f y)" by simp
    thus "x = y" using gf_id by simp
  qed
qed

end
