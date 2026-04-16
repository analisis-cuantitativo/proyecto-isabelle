theory EmptySetUniqueness
  imports Main
begin

(* Uniqueness of the empty set:
   Any two sets with no elements are equal *)

lemma empty_set_uniqueness:
  assumes "(\<forall>x. x \<notin> A)" and "(\<forall>x. x \<notin> B)"
  shows "A = B"
  using assms by auto

(* Alternative formulation:
   Any set with no elements equals the empty set *)

lemma empty_set_uniqueness':
  assumes "\<forall>x. x \<notin> A"
  shows "A = {}"
  using assms by auto

(* Yet another formulation using set equality *)

lemma empty_set_uniqueness'':
  assumes "A = {}" and "B = {}"
  shows "A = B"
  using assms by simp

end
