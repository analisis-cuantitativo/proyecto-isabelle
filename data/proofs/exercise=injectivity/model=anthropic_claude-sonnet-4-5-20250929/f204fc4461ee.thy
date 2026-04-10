theory InjectiveLeftInverse
  imports Main
begin

theorem injective_iff_left_inverse:
  fixes f :: "'a ⇒ 'b"
  shows "inj f ⟷ (∃g :: 'b ⇒ 'a. ∀x. g (f x) = x)"
proof
  (* Forward direction: if f is injective, then there exists a left inverse *)
  assume inj_f: "inj f"
  show "∃g :: 'b ⇒ 'a. ∀x. g (f x) = x"
  proof -
    (* We can use inv_into to construct the left inverse *)
    define g where "g = inv_into UNIV f"
    have "∀x. g (f x) = x"
      using inj_f g_def by (simp add: inv_into_f_f)
    thus ?thesis by blast
  qed
next
  (* Backward direction: if there exists a left inverse, then f is injective *)
  assume "∃g :: 'b ⇒ 'a. ∀x. g (f x) = x"
  then obtain g where g_prop: "∀x. g (f x) = x" by auto
  show "inj f"
  proof (rule injI)
    fix x y
    assume "f x = f y"
    hence "g (f x) = g (f y)" by simp
    with g_prop show "x = y" by simp
  qed
qed

end
