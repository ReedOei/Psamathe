theory Resources
  imports Main Types "HOL-Library.Multiset"
begin

datatype Val = Num nat | Bool bool | Table "Val multiset"
type_synonym Resource = "BaseTy \<times> Val"

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal natural = Num 0"
| "emptyVal boolean = Bool False"
| "emptyVal (table keys t) = Table {#}"
| "emptyVal (named name baseT) = emptyVal baseT"

fun resourceSum :: "Resource option \<Rightarrow> Resource option \<Rightarrow> Resource option" (infix "+\<^sub>r" 65) where
  "(Some (t1, Num n1))    +\<^sub>r (Some (t2, Num n2))    = (if t1 \<approx> t2 then Some (t1, Num (n1 + n2)) else None)"
| "(Some (t1, Bool b1))   +\<^sub>r (Some (t2, Bool b2))   = (if t1 \<approx> t2 then Some (t1, Bool (b1 \<or> b2)) else None)"
| "(Some (t1, Table vs1)) +\<^sub>r (Some (t2, Table vs2)) = (if t1 \<approx> t2 then Some (t1, Table (vs1 + vs2)) else None)"
| "_ +\<^sub>r _ = None"

fun resourceSub :: "Resource option \<Rightarrow> Resource option \<Rightarrow> Resource option" (infix "-\<^sub>r" 65) where
  "(Some (t1, Num n1))    -\<^sub>r (Some (t2, Num n2))    = 
    (if t1 \<approx> t2 \<and> n1 \<ge> n2 then Some (t1, Num (n1 - n2)) else None)"
| "(Some (t1, Bool b1))   -\<^sub>r (Some (t2, Bool b2))   = 
    (if t1 \<approx> t2 \<and> (b2 \<longrightarrow> b1) then 
        if b2 then Some (t1, Bool False) 
     else Some (t1, Bool b1) else None)"
| "(Some (t1, Table vs1)) -\<^sub>r (Some (t2, Table vs2)) = 
    (if t1 \<approx> t2 \<and> vs2 \<subseteq># vs1 then
      Some (t1, Table (vs1 - vs2))
     else None)"
| "_ -\<^sub>r _ = None"

lemma res_add_compat:
  assumes "(Some (t1,v1) +\<^sub>r Some (t2,v2)) \<noteq> None"
  shows "t1 \<approx> t2"
  using assms
  apply (cases v1, auto)
  apply (cases v2, auto)
  apply (cases "t1 \<approx> t2", auto)
  apply (cases v2, auto)
  apply (cases "t1 \<approx> t2", auto)
  apply (cases v2, auto)
  by (cases "t1 \<approx> t2", auto)

lemma res_sub_compat:
  assumes "(Some (t1,v1) -\<^sub>r Some (t2,v2)) \<noteq> None"
  shows "t1 \<approx> t2"
  using assms
  apply (cases v1, auto)
  apply (cases v2, auto)
  apply (cases "t1 \<approx> t2", auto)
  apply (cases v2, auto)
  apply (cases "t1 \<approx> t2", auto)
  apply (cases v2, auto)
  by (cases "t1 \<approx> t2", auto)

lemma res_cancel:
  assumes "(r1 -\<^sub>r r2) \<noteq> None"
  shows "(r1 -\<^sub>r r2) +\<^sub>r r2 = r1"
  using assms
proof(cases r1)
  case None
  then show ?thesis by simp
next
  case (Some x1)
  then obtain t1 v1 where a1: "x1 = (t1,v1)" by (cases x1)
  then obtain t2 v2 where a2: "r2 = Some (t2,v2)"
    by (metis assms old.prod.exhaust option.collapse resourceSub.simps(11))
  then show ?thesis using a1 Some assms
    apply (cases v1, auto) 
    apply (cases v2, auto)
    apply (metis le_add_diff_inverse2 option.distinct(1) resourceSum.simps(1))
    apply (cases v2, auto)
    apply (smt assms resourceSub.simps(2) resourceSum.simps(2))
    apply (cases v2, auto)
    by (metis option.discI resourceSum.simps(3) subset_mset.diff_add)
qed

fun demoteResource :: "Resource option \<Rightarrow> Resource option" where
  "demoteResource (Some (t, Num n)) = Some (demote\<^sub>* t, Num n)"
| "demoteResource (Some (t, Bool b)) = Some (demote\<^sub>* t, Bool b)"
| "demoteResource (Some (t, Table vs)) = Some (demote\<^sub>* t, Table vs)"
| "demoteResource None = None"

fun exactType :: "Resource option \<Rightarrow> Type option" where
  "exactType (Some (t, Num n)) = Some (toQuant n, t)"
| "exactType (Some (t, Bool b)) = Some (if b then (one, t) else (empty, t))"
| "exactType (Some (t, Table vs)) = Some (toQuant (size vs), t)"
| "exactType None = None"

(* TODO: Update when adding more types *)
fun baseTypeMatches :: "BaseTy \<Rightarrow> Val \<Rightarrow> bool" where
  "baseTypeMatches natural (Num _) = True"
| "baseTypeMatches boolean (Bool _) = True"
(* TODO: The table case might need to be more specific, and say that all the values also match the specified type... *)
| "baseTypeMatches (table _ _) (Table _) = True"
| "baseTypeMatches (named name baseT) v = baseTypeMatches baseT v"
| "baseTypeMatches _ _ = False"

lemma baseTypeMatches_emptyVal_works: "baseTypeMatches t (emptyVal t)"
  by (induction t, auto)

lemma exactType_table_len:
  assumes "exactType (Some (t, Table vs)) = Some (q, t)"
  shows "toQuant (size vs) \<sqsubseteq> q"
  using assms
  by (simp add: less_general_quant_refl)

lemma quant_add[simp]: "toQuant (n + m) = toQuant n \<oplus> toQuant m"
  by (auto simp: toQuant_def)

lemma quant_add_comm: "q \<oplus> r = r \<oplus> q"
  by (smt TyQuant.exhaust addQuant.simps(1) addQuant.simps(10) addQuant.simps(12) addQuant.simps(2) addQuant.simps(3) addQuant.simps(4) addQuant.simps(5) addQuant.simps(6) addQuant.simps(8) addQuant.simps(9))

lemma quant_add_lt_left:
  assumes "r \<sqsubseteq> r'"
  shows "q \<oplus> r \<sqsubseteq> q \<oplus> r'"
  using assms
  apply (cases q, auto)
  apply (smt TyQuant.exhaust addQuant.simps(1) addQuant.simps(2) addQuant.simps(3) addQuant.simps(4))
  apply (metis TyQuant.distinct(11) TyQuant.distinct(3) TyQuant.distinct(5) TyQuant.distinct(7) TyQuant.distinct(9) TyQuant.exhaust addQuant.simps(1) addQuant.simps(12) addQuant.simps(13) addQuant.simps(8) assms less_general_quant.simps(1) less_general_quant.simps(10) less_general_quant.simps(12) less_general_quant.simps(13) less_general_quant.simps(6) less_general_quant.simps(9) less_general_quant_refl less_general_quant_trans)
  apply (smt TyQuant.exhaust addQuant.simps(1) addQuant.simps(10) addQuant.simps(11) addQuant.simps(9) insert_iff less_general_quant.simps(11) less_general_quant.simps(2) less_general_quant.simps(4) less_general_quant.simps(5) less_general_quant_refl singletonD)
  by (smt TyQuant.exhaust addQuant.simps(1) addQuant.simps(5) addQuant.simps(6) addQuant.simps(7) less_general_quant.simps(7))

lemma approx_quant_add_lt:
  assumes "toQuant n \<sqsubseteq> q" and "toQuant m \<sqsubseteq> r"
  shows "toQuant (n + m) \<sqsubseteq> q \<oplus> r"
  by (metis assms(1) assms(2) less_general_quant_trans quant_add quant_add_comm quant_add_lt_left)

lemma exactType_of_empty[simp]:
  shows "exactType (Some (t, emptyVal t)) = Some (empty, t)"
proof(induction t)
  case natural
  then show ?case by auto
next
  case boolean
  then show ?case by auto
next
  case (table x1 x2)
  then show ?case by auto
next
  case (named x1 t)
  then show ?case by (cases "emptyVal t", auto)
qed


(* TODO: This is kind of annoying, but I'm not sure if there's any other way to write this... *)
lemma baseTypeMatches_unique_val_Num:
  assumes "baseTypeMatches t (Num n)"
  shows "\<not>(baseTypeMatches t (Bool b))" and "\<not>(baseTypeMatches t (Table vs))"
  using assms
  by (induction t, auto)

lemma baseTypeMatches_unique_val_Bool:
  assumes "baseTypeMatches t (Bool b)"
  shows "\<not>(baseTypeMatches t (Num n))" and "\<not>(baseTypeMatches t (Table vs))"
  using assms
  by (induction t, auto)

lemma baseTypeMatches_unique_val_Table:
  assumes "baseTypeMatches t (Table vs)"
  shows "\<not>(baseTypeMatches t (Bool b))" and "\<not>(baseTypeMatches t (Num n))"
  using assms
  by (induction t, auto)

lemma resource_add_same_base_type:
  assumes "baseTypeMatches t v1" and "baseTypeMatches t v2"
  shows "\<exists>q'. exactType (Some (t,v1) +\<^sub>r Some (t,v2)) = Some (q',t)"
  using assms
  apply (cases v1)
  apply (cases v2, auto simp: baseTypeMatches_unique_val_Num)
  apply (cases v2, auto simp: baseTypeMatches_unique_val_Bool)
  by (cases v2, auto simp: baseTypeMatches_unique_val_Table)

lemma resourceSub_self_emptyVal:
  assumes "baseTypeMatches t v"
  shows "Some (t,v) -\<^sub>r Some (t,v) = Some (t, emptyVal t)"
  using assms
  apply (induction t)
  apply (cases v, auto)
  apply (cases v, auto)
   apply (cases v, auto)
  apply (cases v, auto)
  by (metis (full_types) option.inject prod.inject)

lemma resourceSub_empty_quant_res:
  shows "exactType (Some (t,v) -\<^sub>r Some (t,v)) = Some (empty,t)"
  by (cases v, auto)



lemma demoteBaseType_idem[simp]: "demote\<^sub>* (demote\<^sub>* t) = demote\<^sub>* t"
  by (induction t, auto)

lemma demote_idem[simp]: "demote (demote \<tau>) = demote \<tau>"
  by (cases \<tau>, auto)

lemma exactType_preserves_tyquant:
  shows "\<exists>q. exactType (Some (t, v)) = Some (q, t)"
  by (cases v, auto)

lemma exactType_has_same_base_type:
  assumes "exactType r = Some (q, t)"
  obtains v where "r = Some (t, v)"
  using assms
  apply (cases r, auto)
  by (metis exactType_preserves_tyquant option.inject prod.inject)

lemma baseTypeMatches_nums:
  assumes "baseTypeMatches t (Num n)"
  shows "baseTypeMatches t (Num m)"
  using assms
  by (induction t, auto)

lemma baseTypeMatches_bools:
  assumes "baseTypeMatches t (Bool n)"
  shows "baseTypeMatches t (Bool m)"
  using assms
  by (induction t, auto)

lemma baseTypeMatches_tables:
  assumes "baseTypeMatches t (Table vs)" and "ws \<subseteq># vs"
  shows "baseTypeMatches t (Table ws)"
  using assms
  by (induction t, auto)

lemma demoteResource_matches:
  assumes "baseTypeMatches t v"
  obtains t' v' where "demoteResource (Some (t, v)) = Some (t', v')" and "baseTypeMatches t' v'"
  using assms
  apply (induction t)
  by (cases v, auto)+

(* TODO: This will have to change if/when we update baseTypeMatches to actually care about 
         the types of things in the table *)
lemma baseTypeMatches_table_prepend:
  assumes "baseTypeMatches t2 (Table vs)"
      and "baseTypeMatches t1 v1"
      (* and t2 = table _ (q,t1); also handle the named type case *)      
    shows "baseTypeMatches t2 (Table ({#v1#} + vs))"
  using assms
  by (induction t2, auto)

lemma resourceSub_empty_quant:
  assumes "exactType r = Some (q,t)"
  shows "exactType (r -\<^sub>r r) = Some (empty,t)"
  using assms
  apply (cases r, auto)
  using exactType_has_same_base_type resourceSub_empty_quant_res by auto

lemma res_add_ty_first_res:
  assumes "exactType (Some (t1,v1)) = Some (q,t1)" 
    and "exactType (Some (t2,v2)) = Some (r,t2)" 
    and "(Some (t1,v1) +\<^sub>r Some (t2,v2)) \<noteq> None"
  shows "\<exists>q'. exactType (Some (t1,v1) +\<^sub>r Some (t2,v2)) = Some (q', t1)"
  using assms
  apply (cases v1, auto)
  apply (cases v2, auto)
  apply (metis exactType.simps(1) option.distinct(1))
  apply (cases v2, auto)
  apply (metis exactType_preserves_tyquant option.distinct(1))
  apply (cases v2, auto)
  by (metis exactType.simps(3) option.distinct(1))

lemma baseTypeMatches_add:
  assumes "baseTypeMatches t1 v1" 
      and "baseTypeMatches t2 v2"
      and "t1 \<approx> t2"
      and "Some (t1,v1) +\<^sub>r Some (t2,v2) = Some (t1,v)"
    shows "baseTypeMatches t1 v"
  using assms
  apply (cases v1)
  apply (cases v2, auto)
  using baseTypeMatches_nums apply blast
  apply (cases v2, auto)
  using baseTypeMatches_bools apply blast
  apply (cases v2, auto)
  sorry

lemma baseTypeMatches_store_add:
  assumes store_ok: "\<forall>l t v. \<rho> l = Some (t, v) \<longrightarrow> baseTypeMatches t v"
      and "\<rho> l +\<^sub>r \<rho> k = Some (t,v)"
    shows "baseTypeMatches t v"
proof -
  obtain tl vl tk vk
    where "\<rho> l = Some (tl, vl)" and "baseTypeMatches tl vl"
      and "\<rho> k = Some (tk, vk)" and "baseTypeMatches tk vk"
    using assms
    by (metis option.exhaust resourceSum.simps(11) resourceSum.simps(4) surj_pair)

  then show ?thesis
    by (smt assms(2) baseTypeMatches_add eq_snd_iff exactType_preserves_tyquant option.distinct(1) option.inject res_add_compat res_add_ty_first_res)
qed

lemma res_add_ty_first:
  assumes "exactType r1 = Some (q,t1)" 
    and "exactType r2 = Some (r,t2)" 
    and "r1 +\<^sub>r r2 \<noteq> None"
  shows "\<exists>q'. exactType (r1 +\<^sub>r r2) = Some (q', t1)"
  using assms
  apply (cases r1, auto)
  apply (cases r2, auto)
  by (metis (no_types, lifting) assms(3) exactType_has_same_base_type res_add_ty_first_res)

lemma exactType_add_res:
  assumes "exactType (Some (t1,v1)) = Some (q,t1)" 
    and "exactType (Some (t2,v2)) = Some (r,t2)"
    and "t1 \<approx> t2"
    and "exactType (Some (t1,v1) +\<^sub>r Some (t2,v2)) = Some (q', t1)"
  shows "q' \<sqsubseteq> q \<oplus> r"
proof (cases v1)
  case (Num x1)
  then show ?thesis using assms
    apply (cases v2, auto)
    by (simp add: less_general_quant_refl)
next
  case (Bool x2)
  then show ?thesis using assms
    apply (cases v2, auto)
    apply (cases x2, auto)
     apply (cases r, auto)
    by (metis Pair_inject addQuant.simps(1) addQuant.simps(3) less_general_quant_refl)
next
  case (Table x3)
  then show ?thesis using assms
    apply (cases v2, auto)
    by (simp add: less_general_quant_refl)
qed

lemma exactType_add:
  assumes "exactType r1 = Some (q,t1)" 
    and "exactType r2 = Some (r,t2)"
    and "t1 \<approx> t2"
    and "exactType (r1 +\<^sub>r r2) = Some (q', t1)"
  shows "q' \<sqsubseteq> q \<oplus> r"
  using assms
  by (metis exactType_add_res exactType_has_same_base_type)

lemma addQuant_less_general:
  assumes "q \<sqsubseteq> q'" and "r \<sqsubseteq> r'"
  shows "q \<oplus> r \<sqsubseteq> q' \<oplus> r'"
  using assms
  by (metis less_general_quant_trans quant_add_comm quant_add_lt_left)

end
