theory InjectiveLeftInverse
  imports Main
begin

(* Formalization: f is injective iff there exists a left inverse g *)
theorem injective_iff_left_inverse:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "inj f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
proof
  (* Forward direction: if f is injective, then there exists a left inverse *)
  assume "inj f"
  then show "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  proof -
    (* We need to construct g using the axiom of choice *)
    (* For each y in B, if y is in the range of f, pick the unique x such that f(x) = y *)
    (* Otherwise, pick an arbitrary element (we use SOME) *)

    (* First, we show that for elements in the range, there's a unique preimage *)
    have "\<forall>y. \<exists>!x. f x = y \<or> (\<forall>z. f z \<noteq> y)"
      by auto

    (* Define g using Hilbert's choice operator *)
    define g where "g = (\<lambda>y. SOME x. f x = y)"

    (* Show that g is a left inverse *)
    have "\<forall>x. g (f x) = x"
    proof
      fix x
      have "f x = f x" by simp
      then have "f x = f x \<and> (\<forall>z. f z = f x \<longrightarrow> z = x)"
        using \<open>inj f\<close> by (simp add: inj_def)
      then have "(SOME z. f z = f x) = x"
        by (rule someI2[where a=x]) auto
      then show "g (f x) = x"
        unfolding g_def by simp
    qed

    then show ?thesis by blast
  qed
next
  (* Backward direction: if there exists a left inverse, then f is injective *)
  assume "\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x"
  then obtain g where g_prop: "\<forall>x. g (f x) = x" by blast

  show "inj f"
    unfolding inj_def
  proof (intro allI impI)
    fix x y
    assume "f x = f y"
    then have "g (f x) = g (f y)" by simp
    then show "x = y" using g_prop by simp
  qed
qed

(* Alternative formulation using function composition *)
theorem injective_iff_left_inverse_comp:
  fixes f :: "'a \<Rightarrow> 'b"
  shows "inj f \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. g \<circ> f = id)"
proof -
  have "(\<exists>g :: 'b \<Rightarrow> 'a. g \<circ> f = id) \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. (g \<circ> f) x = id x)"
    by auto
  also have "... \<longleftrightarrow> (\<exists>g :: 'b \<Rightarrow> 'a. \<forall>x. g (f x) = x)"
    by auto
  also have "... \<longleftrightarrow> inj f"
    using injective_iff_left_inverse by simp
  finally show ?thesis by simp
qed

end
