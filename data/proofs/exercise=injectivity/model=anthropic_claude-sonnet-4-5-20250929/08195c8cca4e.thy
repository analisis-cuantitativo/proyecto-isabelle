theory Injective_LeftInverse
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
    then have "g (f x) = g (f y)" by simp
    with g_prop show "x = y" by simp
  qed
next
  assume "inj f"
  then have inj_f: "\<And>x y. f x = f y \<Longrightarrow> x = y" by (simp add: inj_def)

  define g where "g = (\<lambda>y. SOME x. f x = y)"

  have "\<forall>x. g (f x) = x"
  proof
    fix x
    have "f x = f x" by simp
    then have "\<exists>z. f z = f x" by auto
    then have "(SOME z. f z = f x) = x"
      by (rule someI2) (auto simp add: inj_f)
    then show "g (f x) = x" unfolding g_def by simp
  qed

  then show "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x" by auto
qed

end
