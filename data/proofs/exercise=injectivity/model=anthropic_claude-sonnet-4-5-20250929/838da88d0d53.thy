theory InjectiveLeftInverse
  imports Main
begin

(* Formalization: f is injective iff there exists a left inverse g *)
theorem injective_iff_left_inverse:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "inj f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
proof
  (* Forward direction: if f is injective, then there exists a left inverse *)
  assume "inj f"
  then show "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  proof -
    (* We need to construct g. For elements in the range of f, we can invert f.
       For elements outside the range, we pick an arbitrary element (using SOME). *)
    obtain a0 :: 'a where "True" by auto

    define g :: "'b \<Rightarrow> 'a" where
      "g = (\<lambda>y. if y \<in> range f then (THE x. f x = y) else a0)"

    have "\<forall>x. g (f x) = x"
    proof
      fix x :: 'a
      have "f x \<in> range f" by auto
      moreover have "(THE x'. f x' = f x) = x"
      proof (rule the_equality)
        show "f x = f x" by simp
      next
        fix x' assume "f x' = f x"
        with \<open>inj f\<close> show "x' = x"
          unfolding inj_def by auto
      qed
      ultimately show "g (f x) = x"
        unfolding g_def by simp
    qed

    thus ?thesis by blast
  qed
next
  (* Backward direction: if there exists a left inverse, then f is injective *)
  assume "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  then obtain g :: "'b \<Rightarrow> 'a" where g_prop: "\<forall>x. g (f x) = x" by auto

  show "inj f"
    unfolding inj_def
  proof (intro allI impI)
    fix x y :: 'a
    assume "f x = f y"
    hence "g (f x) = g (f y)" by simp
    with g_prop show "x = y" by simp
  qed
qed

end
