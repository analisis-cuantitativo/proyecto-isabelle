theory InjectiveLeftInverse
  imports Main
begin

lemma injective_iff_left_inverse:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "inj f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
proof
  assume "inj f"
  then show "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  proof -
    (* We need to construct a left inverse g *)
    (* For elements in the range of f, we can use inv_into to get a preimage *)
    (* For elements outside the range, we pick an arbitrary element (using SOME) *)
    obtain a0 :: 'a where "True" by auto
    define g :: "'b \<Rightarrow> 'a" where
      "g = (\<lambda>y. if y \<in> range f then inv_into UNIV f y else a0)"

    have "\<forall>x. g (f x) = x"
    proof
      fix x :: 'a
      have "f x \<in> range f" by auto
      then have "g (f x) = inv_into UNIV f (f x)"
        unfolding g_def by simp
      also have "... = x"
        using \<open>inj f\<close> by (simp add: inv_into_f_f)
      finally show "g (f x) = x" .
    qed
    thus ?thesis by blast
  qed
next
  assume "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  then obtain g :: "'b \<Rightarrow> 'a" where g_prop: "\<forall>x. g (f x) = x" by blast

  show "inj f"
  proof (rule injI)
    fix x y :: 'a
    assume "f x = f y"
    then have "g (f x) = g (f y)" by simp
    with g_prop show "x = y" by simp
  qed
qed

end
