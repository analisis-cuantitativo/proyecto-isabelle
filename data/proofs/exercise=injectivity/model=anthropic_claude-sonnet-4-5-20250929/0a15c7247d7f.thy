theory FunctionInjectivity
  imports Main
begin

lemma injective_iff_left_inverse:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "inj f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
proof
  assume "inj f"
  (* For each y in B, if y is in the range of f, pick the unique x with f(x) = y.
     Otherwise, pick an arbitrary value (using SOME). *)
  define g where "g = (\<lambda>y. SOME x. f x = y)"
  have "\<forall>x. g (f x) = x"
  proof
    fix x
    from \<open>inj f\<close> have "f x = f x" by simp
    then have "(SOME x'. f x' = f x) = x"
      using \<open>inj f\<close> unfolding inj_def
      by (metis (mono_tags, lifting) someI_ex)
    thus "g (f x) = x"
      unfolding g_def by simp
  qed
  thus "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
    by blast
next
  assume "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  then obtain g where g_prop: "\<forall>x. g (f x) = x"
    by auto
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
