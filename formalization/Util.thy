theory Util
  imports Main "HOL-Library.Multiset" Types
begin

(* Facts about built-in constructs that aren't in the standard library *)

lemma comp_id_nop: "foldl (\<circ>) f (replicate n id) = f"
  by (induction n, auto)

lemma foldl_comp: "foldl (\<circ>) (foldl (\<circ>) id xs) ys a = foldl (\<circ>) id xs (foldl (\<circ>) id ys a)"
  apply (induction ys arbitrary: xs)
  apply simp
  by (metis comp_apply foldl_Cons foldl_Nil fun.map_id0 id_apply)

lemma multiset_elem_length:
  assumes "x \<in># xs"
  shows "size xs \<ge> 1"
  using assms
  by (induction xs, auto)

lemma multiset_elem_tyquant:
  assumes "x \<in># xs"
  shows "one \<sqsubseteq> toQuant (size xs)"
  using assms
  by (auto simp: toQuant_def)

end