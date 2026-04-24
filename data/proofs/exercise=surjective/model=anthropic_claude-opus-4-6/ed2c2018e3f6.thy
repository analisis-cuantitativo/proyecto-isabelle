theory SurjectiveRightInverse
  imports Main
begin

theorem surj_iff_has_right_inverse:
  "surj f \<longleftrightarrow> (\<exists>g. f \<circ> g = id)"
proof
  assume "surj f"
  then have witness: "\<And>y. \<exists>x. f x = y"
    unfolding surj_def by auto
  have "f \<circ> (\<lambda>y. SOME x. f x = y) = id"
  proof (rule ext)
    fix y
    show "(f \<circ> (\<lambda>y. SOME x. f x = y)) y = id y"
      using someI_ex[OF witness[of y]] by simp
  qed
  then show "\<exists>g. f \<circ> g = id"
    by blast
next
  assume "\<exists>g. f \<circ> g = id"
  then obtain g where fg: "f \<circ> g = id"
    by blast
  show "surj f"
  proof (rule surjI)
    fix y
    from fg have "f (g y) = y"
      by (simp add: fun_eq_iff)
    then show "f (g y) = y" .
  qed
qed

end
