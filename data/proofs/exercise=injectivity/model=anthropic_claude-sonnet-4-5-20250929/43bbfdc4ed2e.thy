theory InjectiveLeftInverse
  imports Main
begin

theorem injective_iff_left_inverse:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "inj f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
proof
  assume "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  then obtain g where g_prop: "\<forall>x. g (f x) = x" by auto
  show "inj f"
  proof (rule injI)
    fix x y
    assume "f x = f y"
    hence "g (f x) = g (f y)" by simp
    with g_prop show "x = y" by simp
  qed
next
  assume "inj f"
  show "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  proof (cases "\<exists>a. True")
    case True
    then obtain a0 :: 'a where "True" by auto
    define g where "g = (\<lambda>y. if y \<in> range f then inv_into UNIV f y else a0)"
    have "\<forall>x. g (f x) = x"
    proof
      fix x
      have "f x \<in> range f" by simp
      with g_def have "g (f x) = inv_into UNIV f (f x)" by simp
      also have "... = x"
        using \<open>inj f\<close> by (simp add: inv_into_f_f)
      finally show "g (f x) = x" .
    qed
    thus ?thesis by auto
  qed
qed

end
