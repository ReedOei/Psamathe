theory Types
  imports Main
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = natural | boolean 
  | table "string list" "TyQuant \<times> BaseTy"
  | named string BaseTy (* TODO: Need to add modifiers *)
type_synonym Type = "TyQuant \<times> BaseTy"

definition toQuant :: "nat \<Rightarrow> TyQuant" where
  "toQuant n \<equiv> (if n = 0 then empty else if n = 1 then one else nonempty)"

lemma toQuant_empty[simp]: "toQuant 0 = empty"
  by (auto simp: toQuant_def)

lemma toQuant_one[simp]: "toQuant (Suc 0) = one"
  by (auto simp: toQuant_def)

fun addQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> TyQuant" (infix "\<oplus>" 60) where
  "(q \<oplus> empty) = q"
| "(empty \<oplus> q) = q"
| "(nonempty \<oplus> r) = nonempty"
| "(r \<oplus> nonempty) = nonempty"
| "(one \<oplus> r) = nonempty"
| "(r \<oplus> one) = nonempty"
| "(any \<oplus> any) = any"

fun demoteBase :: "BaseTy \<Rightarrow> BaseTy" ("demote\<^sub>*") 
  and demote :: "Type \<Rightarrow> Type"  where
  "demote\<^sub>* natural = natural"
| "demote\<^sub>* boolean = boolean"
| "demote\<^sub>* (table keys \<tau>) = table keys (demote \<tau>)"
| "demote\<^sub>* (named name baseTy) = demote\<^sub>* baseTy"
| "demote (q, t) = (q, demote\<^sub>* t)"

fun base_type_compat :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> bool" (infix "\<approx>" 50) where
  "base_type_compat natural natural = True"
| "base_type_compat boolean boolean = True"
| "base_type_compat (table ks1 (q1,t1)) (table ks2 (q2,t2)) = base_type_compat t1 t2"
| "base_type_compat (named name1 baseT1) (named name2 baseT2) = (name1 = name2 \<and> baseT1 = baseT2)"
| "base_type_compat _ _ = False"

lemma base_type_compat_refl[simp]:
  fixes t
  shows "t \<approx> t"
  by (induction t, auto)

lemma base_type_compat_sym:
  fixes t1 and t2
  assumes "t1 \<approx> t2"
  shows "t2 \<approx> t1"
  using assms
proof(induction t1 arbitrary: t2)
  case natural
  then show ?case by (cases t2, auto)
next
  case boolean
  then show ?case by (cases t2, auto)
next
  case (table k1 e1)
  then obtain q1 and t1e where "e1 = (q1,t1e)" by (cases e1)
  then show ?case using table by (cases t2, auto)
next
  case (named x1 t1)
  then show ?case using base_type_compat.elims(2) by auto
qed

lemma base_type_compat_trans: 
  fixes t1 and t2 and t3
  assumes "t1 \<approx> t2" and "t2 \<approx> t3"
  shows "t1 \<approx> t3"
  using assms
proof(induction t1 arbitrary: t2 t3)
  case natural
  then show ?case by (cases t2, cases t3, auto)
next
  case boolean
  then show ?case by (cases t2, cases t3, auto)
next
  case (table k1 e1)
  (* TODO: Pretty gross, can we improve? *)
  then obtain q1 t1e and k2 q2 t2e and k3 q3 t3e 
    where "e1 = (q1,t1e)" and "t2 = table k2 (q2,t2e)" and "t3 = table k3 (q3,t3e)"
    by (metis BaseTy.exhaust base_type_compat.simps(10) base_type_compat.simps(17) base_type_compat.simps(6) base_type_compat_sym demote.cases table.prems(1) table.prems(2))
  then show ?case using table by fastforce
next
  case (named x1 t1)
  then show ?case using base_type_compat.elims(2) by blast
qed

fun less_general_quant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "less_general_quant q any = True"
| "less_general_quant one r = (r \<in> {one, nonempty})"
| "less_general_quant nonempty r = (r = nonempty)"
| "less_general_quant empty r = (r = empty)"
| "less_general_quant any r = (r = any)"

(* TODO: Rename to subtype, probably *)
fun less_general_type :: "Type \<Rightarrow> Type \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>\<tau>" 50) where
  "less_general_type (q,t) (r,u) = (q \<sqsubseteq> r \<and> t \<approx> u)"

lemma less_general_quant_refl: "q \<sqsubseteq> q"
  by (cases q, auto)

lemma less_general_quant_antisym: 
  assumes "q \<sqsubseteq> r" and "r \<sqsubseteq> q"
  shows "q = r"
  using assms
  apply (cases q, auto)
  by (cases r, auto)+

lemma less_general_quant_trans:
  assumes "q1 \<sqsubseteq> q2" and "q2 \<sqsubseteq> q3"
  shows "q1 \<sqsubseteq> q3"
  using assms
  apply (cases q1, auto)
  apply (cases q2, auto, cases q3, auto)+
  by (cases q2, auto)

lemma less_general_type_refl: "\<tau> \<sqsubseteq>\<^sub>\<tau> \<tau>"
  apply (cases \<tau>)
  by (simp add: less_general_quant_refl)

(* NOTE: Not quite antisymmetry, but close *)
lemma less_general_type_antisym: 
  assumes "(q1,t1) \<sqsubseteq>\<^sub>\<tau> (q2,t2)" and "(q2,t2) \<sqsubseteq>\<^sub>\<tau> (q1,t1)"
  shows "q1 = q2" and "t1 \<approx> t2"
  using assms
  by (auto simp: less_general_quant_antisym)

lemma less_general_type_trans:
  assumes "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>" and "\<sigma> \<sqsubseteq>\<^sub>\<tau> \<pi>"
  shows "\<tau> \<sqsubseteq>\<^sub>\<tau> \<pi>"
  using assms
  apply (cases \<tau>, cases \<sigma>, cases \<pi>)
  by (auto simp: less_general_quant_trans base_type_compat_trans)

instantiation TyQuant :: linorder
begin
fun less_eq_TyQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> bool" where
  "less_eq_TyQuant empty r = True"
| "less_eq_TyQuant any r = (r \<notin> {empty})"
| "less_eq_TyQuant one r = (r \<notin> {empty,any})"
 (* Kind of redundant for now, but if we put every back (or otherwise extend the system), it will not be *)
| "less_eq_TyQuant nonempty r = (r \<notin> {empty,any,one})"

fun less_TyQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> bool" where
  "less_TyQuant q r = ((q \<le> r) \<and> (q \<noteq> r))"

instance
proof
  fix x y :: TyQuant
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" 
    by (cases x, (cases y, auto)+)
next
  fix x :: TyQuant
  show "x \<le> x" by (cases x, auto)
next
  fix x y z :: TyQuant
  assume "x \<le> y" and "y \<le> z"
  then show "x \<le> z" by (cases x, (cases y, cases z, auto)+)
next
  fix x y :: TyQuant
  assume "x \<le> y" and "y \<le> x"
  then show "x = y" by (cases x, (cases y, auto)+)
next
  fix x y :: TyQuant
  show "x \<le> y \<or> y \<le> x" by (cases x, (cases y, auto)+)
qed
end
lemma demoteBaseType_base_type_compat:
  assumes "t1 \<approx> t2"
  shows "demote\<^sub>* t1 \<approx> demote\<^sub>* t2"
  using assms
proof(induction t1 arbitrary: t2)
  case natural
  then show ?case by (cases t2, auto)
next
  case boolean
  then show ?case by (cases t2, auto)
next
  case (table x1 x2)
  then show ?case
    apply (cases x2, auto)
  proof -
    fix a :: TyQuant and b :: BaseTy
    assume a1: "x2 = (a, b)"
    assume a2: "table x1 (a, b) \<approx> t2"
    obtain ccss :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> char list list" and tt :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> TyQuant" and bb :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> BaseTy" and ccssa :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> char list list" and tta :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> TyQuant" and bba :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> BaseTy" where
      f3: "\<forall>x0 x1a. (\<exists>v2 v3 v4 v5 v6 v7. x1a = table v2 (v3, v4) \<and> x0 = table v5 (v6, v7) \<and> v4 \<approx> v7) = (x1a = table (ccss x0 x1a) (tt x0 x1a, bb x0 x1a) \<and> x0 = table (ccssa x0 x1a) (tta x0 x1a, bba x0 x1a) \<and> bb x0 x1a \<approx> bba x0 x1a)"
      by moura
    { assume "table x1 (a, b) \<noteq> natural \<or> t2 \<noteq> natural"
      have "t2 = table (ccssa t2 (table x1 (a, b))) (tta t2 (table x1 (a, b)), bba t2 (table x1 (a, b))) \<or> table x1 (a, b) = boolean \<and> t2 = boolean"
        using f3 a2 base_type_compat.elims(2) by fastforce
      then have "table x1 (a, demote\<^sub>* b) \<approx> demote\<^sub>* t2"
        using a2 a1 by (metis base_type_compat.simps(3) demote.simps demoteBase.simps(3) snd_conv snds.intros table.IH) }
    then show "table x1 (a, demote\<^sub>* b) \<approx> demote\<^sub>* t2"
      by simp
  qed
next
  case (named x1 t1)
  then show ?case
    by (cases t2, auto)
qed

lemma demote_lt:
  assumes "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>"
  shows "demote \<tau> \<sqsubseteq>\<^sub>\<tau> demote \<sigma>"
  using assms
  apply (cases \<tau>, cases \<sigma>, auto)
  by (simp add: demoteBaseType_base_type_compat)

end
