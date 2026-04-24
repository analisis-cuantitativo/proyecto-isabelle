theory InjLeftInverse
  imports Main
begin

theorem inj_iff_left_inverse:
  "inj f \<longleftrightarrow> (\<exists>g. g \<circ> f = id)"
proof
  assume "inj f"
  hence "inv f \<circ> f = id"
    by (simp add: inv_o_cancel)
  thus "\<exists>g. g \<circ> f = id"
    by blast
next
  assume "\<exists>g. g \<circ> f = id"
  then obtain g where "g \<circ> f = id"
    by blast
  show "inj f"
  proof (rule injI)
    fix x y
    assume "f x = f y"
    hence "g (f x) = g (f y)"
      by simp
    hence "(g \<circ> f) x = (g \<circ> f) y"
      by simp
    with \<open>g \<circ> f = id\<close> show "x = y"
      by simp
  qed
qed

end
