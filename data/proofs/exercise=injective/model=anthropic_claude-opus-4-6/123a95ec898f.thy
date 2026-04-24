theory InjectiveLeftInverse
  imports Main
begin

theorem inj_iff_has_left_inverse:
  "inj f \<longleftrightarrow> (\<exists>g. g \<circ> f = id)"
proof
  assume inj: "inj f"
  have "\<And>x. (inv f \<circ> f) x = id x"
    using inv_f_f[OF inj] by simp
  then have "inv f \<circ> f = id"
    by (simp add: fun_eq_iff)
  then show "\<exists>g. g \<circ> f = id" by blast
next
  assume "\<exists>g. g \<circ> f = id"
  then obtain g where g: "g \<circ> f = id" by blast
  show "inj f"
  proof (rule injI)
    fix x y
    assume "f x = f y"
    then have "g (f x) = g (f y)" by simp
    then show "x = y"
      using fun_cong[OF g, simplified comp_apply id_apply] by metis
  qed
qed

end
