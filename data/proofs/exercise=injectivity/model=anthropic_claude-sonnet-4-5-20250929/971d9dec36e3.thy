theory InjectiveLeftInverse
  imports Main
begin

(* Define injectivity *)
definition injective :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "injective f \<longleftrightarrow> (\<forall>x y. f x = f y \<longrightarrow> x = y)"

(* Main theorem: f is injective iff it has a left inverse *)
theorem injective_iff_left_inverse:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "injective f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
proof
  (* Forward direction: injective f \<Longrightarrow> \<exists>g. g \<circ> f = id *)
  assume "injective f"
  then have inj: "\<forall>x y. f x = f y \<longrightarrow> x = y"
    unfolding injective_def by simp

  (* We use the axiom of choice (via SOME) to construct the left inverse *)
  define g where "g = (\<lambda>y. SOME x. f x = y)"

  have "\<forall>x. g (f x) = x"
  proof
    fix x
    have "f x = f x" by simp
    then have "f (SOME z. f z = f x) = f x"
      by (rule someI)
    then have "SOME z. f z = f x = x"
      using inj by auto
    then show "g (f x) = x"
      unfolding g_def by simp
  qed

  thus "\<exists>g. \<forall>x. g (f x) = x" by blast
next
  (* Backward direction: (\<exists>g. g \<circ> f = id) \<Longrightarrow> injective f *)
  assume "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  then obtain g where g_prop: "\<forall>x. g (f x) = x" by blast

  show "injective f"
    unfolding injective_def
  proof (intro allI impI)
    fix x y
    assume "f x = f y"
    then have "g (f x) = g (f y)" by simp
    then show "x = y" using g_prop by simp
  qed
qed

end
