theory EmptySetUniqueness
  imports Main
begin

(* Uniqueness of the empty set:
   If two sets both contain no elements, then they are equal *)

lemma empty_set_unique:
  assumes "∀x. x ∉ A"
  assumes "∀x. x ∉ B"
  shows "A = B"
  using assms by auto

(* Alternative formulation:
   Any set with no elements equals the empty set *)

lemma empty_set_unique':
  assumes "∀x. x ∉ A"
  shows "A = {}"
  using assms by auto

(* Another formulation using set equality:
   If A and B are both empty, they are equal *)

lemma empty_set_unique'':
  assumes "A = {}"
  assumes "B = {}"
  shows "A = B"
  using assms by simp

end
