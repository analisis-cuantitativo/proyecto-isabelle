theory Surjective_RightInverse
  imports Main
begin

theorem surjective_iff_right_inverse:
  "surj f \<longleftrightarrow> (\<exists>g. \<forall>y. f (g y) = y)"
proof
  (* Direction 1: If f is surjective, then f has a right inverse *)
  assume "surj f"
  hence "\<forall>y. \<exists>x. f x = y"
    unfolding surj_def .
  (* Use Hilbert's choice operator to construct the right inverse *)
  hence "\<forall>y. f (SOME x. f x = y) = y"
    using someI_ex by auto
  thus "\<exists>g. \<forall>y. f (g y) = y"
    by blast
next
  (* Direction 2: If f has a right inverse, then f is surjective *)
  assume "\<exists>g. \<forall>y. f (g y) = y"
  then obtain g where "\<forall>y. f (g y) = y"
    by blast
  (* For any y, g(y) is a preimage under f *)
  thus "surj f"
    unfolding surj_def by blast
qed

end
