theory SurjectiveRightInverse
  imports Main
begin

theorem surj_iff_has_right_inverse:
  "surj f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"
proof
  assume S: "surj f"
  define g where "g = (\<lambda>y. SOME x. f x = y)"
  have "\<forall>y. f (g y) = y"
  proof
    fix y
    from S have "\<exists>x. y = f x" by (auto simp: surj_def)
    hence "\<exists>x. f x = y" by auto
    thus "f (g y) = y" unfolding g_def by (rule someI_ex)
  qed
  thus "\<exists>g. \<forall>y. f (g y) = y" by blast
next
  assume "\<exists>g. \<forall>y. f (g y) = y"
  then obtain g where "\<forall>y. f (g y) = y" by blast
  thus "surj f" by (auto simp: surj_def) (metis)
qed

end
