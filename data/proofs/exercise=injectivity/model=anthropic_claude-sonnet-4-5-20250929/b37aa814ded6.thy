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
    thus "x = y" using g_prop by simp
  qed
next
  assume "inj f"
  then have inj_f: "\<And>x y. f x = f y \<Longrightarrow> x = y" by (simp add: inj_def)

  define g where "g = (\<lambda>y. SOME x. f x = y)"

  have g_prop: "\<forall>x. g (f x) = x"
  proof
    fix x
    have "f x = f x" by simp
    hence "\<exists>z. f z = f x" by auto
    hence "f (g (f x)) = f x"
      unfolding g_def by (rule someI[of "\<lambda>z. f z = f x" x], simp)
    thus "g (f x) = x" using inj_f by simp
  qed

  thus "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x" by auto
qed

end
