theory Psamathe
  imports Main "HOL-Library.Rewrite"
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = natural | boolean 
  | table "string list" "TyQuant \<times> BaseTy"
type_synonym Type = "TyQuant \<times> BaseTy"
datatype Mode = s | d
datatype SVal = SLoc nat | Amount nat
type_synonym StorageLoc = "nat \<times> SVal" 
datatype Stored = V string | Loc StorageLoc
datatype Locator = N nat | B bool | S Stored
  | VDef string BaseTy ("var _ : _")
  | EmptyList Type ("[ _ ; ]")
  | ConsList Type "Locator" "Locator" ("[ _ ; _ , _ ]")
datatype Stmt = Flow Locator Locator
datatype Prog = Prog "Stmt list"

type_synonym Env = "(Stored, Type) map"

definition toQuant :: "nat \<Rightarrow> TyQuant" where
  "toQuant n \<equiv> (if n = 0 then empty else if n = 1 then one else nonempty)"

fun addQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> TyQuant" ("_ \<oplus> _") where
  "(q \<oplus> empty) = q"
| "(empty \<oplus> q) = q"
| "(nonempty \<oplus> r) = nonempty"
| "(r \<oplus> nonempty) = nonempty"
| "(one \<oplus> r) = nonempty"
| "(r \<oplus> one) = nonempty"
| "(any \<oplus> any) = any"

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ ; _ : _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} f ; (N n) : (toQuant(n), natural) \<stileturn> \<Gamma>"
| Bool: "\<Gamma> \<turnstile>{s} f ; (B b) : (one, boolean) \<stileturn> \<Gamma>"
| Var: "\<lbrakk> \<Gamma> x = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S x) : \<tau> \<stileturn> (\<Gamma>(x \<mapsto> f(\<tau>)))"
| VarDef: "\<lbrakk> V x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} f ; (var x : t) : (empty, t) \<stileturn> (\<Gamma>(V x \<mapsto> f(empty, t)))"
| EmptyList: "\<Gamma> \<turnstile>{s} f ; [ \<tau> ; ] : (empty, table [] \<tau>) \<stileturn> \<Gamma>"
| ConsList: "\<lbrakk> \<Gamma> \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta> ;
              \<Delta> \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi> \<rbrakk> 
             \<Longrightarrow> \<Gamma> \<turnstile>{s} f ; [ \<tau> ; \<L>, Tail ] : (one \<oplus> q, table [] \<tau>) \<stileturn> \<Xi>"

datatype Val = Num nat | Bool bool 
  | Table "StorageLoc list"
datatype Resource = Res "BaseTy \<times> Val" | error
type_synonym Store = "(string, StorageLoc) map \<times> (nat, Resource) map"

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal natural = Num 0"
| "emptyVal boolean = Bool False"
| "emptyVal (table keys t) = Table []"

fun located :: "Locator \<Rightarrow> bool" where
  "located (S (Loc _)) = True"
| "located [ \<tau> ; ] = True"
| "located [ \<tau> ; Head, Tail ] = (located Head \<and> located Tail)"
| "located _ = False"

inductive loc_eval :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> Locator \<Rightarrow> bool"
  ("< _ , _ > \<rightarrow> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> Res (natural, Num n))), S (Loc (l, Amount n)) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b))), S (Loc (l, SLoc l)) >"
| EVar: "\<lbrakk> \<mu> x = Some l \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), S (V x) > \<rightarrow> < (\<mu>, \<rho>), S (Loc l) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t))), S (Loc (l, SLoc l)) >"
| EConsListHeadCongr: "\<lbrakk> < \<Sigma>, \<L> > \<rightarrow> < \<Sigma>', \<L>' > \<rbrakk>
                   \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<rightarrow> < \<Sigma>', [ \<tau> ; \<L>', Tail ] >"
| EConsListTailCongr: "\<lbrakk> located \<L> ; < \<Sigma>, Tail > \<rightarrow> < \<Sigma>', Tail' > \<rbrakk>
              \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<rightarrow> < \<Sigma>', [ \<tau> ; \<L>, Tail' ] >"

(* TODO: Should replace direct lookup by select, probably. Actually, this rule isn't needed, I think, 
  because we only need to allocate the list if we are flowing from it.
| EConsList: "\<lbrakk> \<rho> tailLoc = Some (table [] \<tau>, Table locs) \<rbrakk>
              \<Longrightarrow> < (\<mu>, \<rho>), [ \<tau> ; S (Loc l), S (Loc (tailLoc, SLoc tailLoc)) ] > 
                  \<rightarrow> < (\<mu>, \<rho>(tailLoc \<mapsto> (table [] \<tau>, Table (l # locs)))), S (Loc (tailLoc, SLoc tailLoc)) >"
*)
(* | EEmptyList: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk>
               \<Longrightarrow> < (\<mu>, \<rho>), [ \<tau> ; ] > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (table [] \<tau>, Table []))), S (Loc (l, SLoc l)) >"
*)

(* Auxiliary definitions *)

(* TODO: Update when adding new types *)
fun base_type_compat :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> bool" where
  "base_type_compat natural natural = True"
| "base_type_compat boolean boolean = True"
| "base_type_compat (table ks1 (q1,t1)) (table ks2 (q2,t2)) = base_type_compat t1 t2"
| "base_type_compat _ _ = False"

lemma base_type_compat_refl:
  fixes t
  shows "base_type_compat t t"
  by (induction t, auto)

lemma base_type_compat_sym:
  fixes t1 and t2
  assumes "base_type_compat t1 t2"
  shows "base_type_compat t2 t1"
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
qed

thm base_type_compat.induct

lemma base_type_compat_trans: 
  fixes t1 and t2 and t3
  assumes "base_type_compat t1 t2" and "base_type_compat t2 t3"
  shows "base_type_compat t1 t3"
  using assms
proof(induction t1 arbitrary: t2 t3)
  case natural
  then show ?case by (cases t2, cases t3, auto)
next
  case boolean
  then show ?case by (cases t2, cases t3, auto)
next
  case (table k1 e1)
  then obtain q1 t1e and k2 q2 t2e and k3 q3 t3e 
    where "e1 = (q1,t1e)" and "t2 = table k2 (q2,t2e)" and "t3 = table k3 (q3,t3e)"
    by (metis BaseTy.distinct(4) BaseTy.inject BaseTy.simps(7) base_type_compat.elims(2))
  then show ?case using table by fastforce
qed

fun selectLoc :: "Store \<Rightarrow> StorageLoc \<Rightarrow> Resource" where
  "selectLoc (\<mu>, \<rho>) (l, Amount n) = 
                              (case \<rho> l of Some (Res (t,_)) \<Rightarrow> Res (t, Num n) | _ \<Rightarrow> error)"
| "selectLoc (\<mu>, \<rho>) (l, SLoc k) = (case \<rho> k of None \<Rightarrow> error | Some r \<Rightarrow> r)"

fun select :: "Store \<Rightarrow> Stored \<Rightarrow> Resource" where
  "select (\<mu>, \<rho>) (V x) = (case \<mu> x of Some l \<Rightarrow> selectLoc (\<mu>, \<rho>) l | None \<Rightarrow> error)"
| "select \<Sigma> (Loc l) = selectLoc \<Sigma> l"

fun ty_res_compat :: "Type \<Rightarrow> Resource \<Rightarrow> bool" where
  "ty_res_compat (q,t1) (Res (t2,_)) = base_type_compat t1 t2"
| "ty_res_compat _ error = False"

fun var_dom :: "Env \<Rightarrow> string set" where
  "var_dom \<Gamma> = { x . V x \<in> dom \<Gamma> }"

(* This is a weaker version of compatibility (tentatively, "locator compatibility")
  This is needed, because while evaluating locators, the type environments won't agree with the 
  actual state of the store,
  because the type environment represents the state of the store *after* the flow occurs. 
  So we will need some separate "statement compatibility" definition, which includes stronger
  conditions on the state of the store (e.g., type quantities being correct, the only strengthening
  I think we will need)*)
fun compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" ("_ \<leftrightarrow> _") where
  "compat \<Gamma> (\<mu>, \<rho>) = ((var_dom \<Gamma> = dom \<mu>) \<and> 
                      (\<forall>x l k. \<mu> x = Some (l, k) \<longrightarrow> \<rho> l \<noteq> None))"
(* TODO: Need to eventually put this next line back. This is the part of type compatibility 
    that I think should be retained by locator evaluation *)
                     (* (\<forall>x q t. \<Gamma> x = Some (q,t) \<longrightarrow> ty_res_compat (q,t) (select (\<mu>, \<rho>) x)))" *)

lemma gen_loc:
  fixes m :: "(nat, 'a) map"
  assumes is_fin: "finite (dom m)"
  obtains "l" where "l \<notin> dom m"
  using ex_new_if_finite is_fin by auto

definition type_preserving :: "(Type \<Rightarrow> Type) \<Rightarrow> bool" where
  "type_preserving f \<equiv> \<forall>\<tau>. base_type_compat (snd \<tau>) (snd (f \<tau>))"

instantiation TyQuant :: linorder
begin

fun less_eq_TyQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> bool" where
  "less_eq_TyQuant empty r = True"
| "less_eq_TyQuant any r = (r \<notin> {empty})"
| "less_eq_TyQuant one r = (r \<notin> {empty,any})"
 (* Kind of redundant for now, but if we put every back, it will not be *)
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

fun less_eq_Type :: "Type \<Rightarrow> Type \<Rightarrow> bool" (infix "\<le>\<^sub>\<tau>" 50) where
  "less_eq_Type (q1,t1) (q2, t2) = (q1 \<le> q2)"

definition mode_compat :: "Mode \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> bool" where
  "mode_compat m f \<equiv> case m of s \<Rightarrow> \<forall>\<tau>. f \<tau> \<le>\<^sub>\<tau> \<tau> | d \<Rightarrow> \<forall>\<tau>. \<tau> \<le>\<^sub>\<tau> f \<tau>"

lemma located_env_compat:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> \<Sigma>"
      and "located \<L>"
      and "type_preserving f"
    shows "\<Delta> \<leftrightarrow> \<Sigma>"
  using assms
proof(induction arbitrary: \<Sigma>)
  case (Nat \<Gamma> f n)
  then show ?case by simp
next
  case (Bool \<Gamma> f b)
  then show ?case by simp
next
  case (Var \<Gamma> x \<tau> m f)
  then have x_in_dom: "x \<in> dom \<Gamma>" by auto
  then show ?case 
  proof(cases x)
    case (V x1)
    then show ?thesis using Var.prems by simp
  next
    case (Loc x2)
    then show ?thesis using Var.prems
      by (cases \<Sigma>, simp add: domIff)
  qed
(*
  This is part of the proof for the full version of locator compatiblity; still unfinished
    then show ?thesis using Var.prems x_in_dom
      apply (cases \<Sigma>, simp add: domIff)
    proof((rule allI)+, clarsimp)
      fix \<mu> \<rho> q t
      assume "type_preserving f"
      then have "base_type_compat (snd (f \<tau>)) t" 
        apply (auto simp: type_preserving_def)
      show "ty_res_compat (q, t) (selectLoc (\<mu>, \<rho>) x2)"
  qed *)
next
  case (VarDef x \<Gamma> f t)
  then show ?case by simp 
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case by simp
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then show ?case by simp 
qed

lemma locator_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
      and "finite (dom \<rho>)"
      and "type_preserving f"
  shows "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. <(\<mu>, \<rho>), \<L>> \<rightarrow> <(\<mu>', \<rho>'), \<L>'> )"
  using assms
proof(induction arbitrary: \<mu> \<rho> m rule: loc_type.induct)
  case (Nat \<Gamma> f n)
  then show ?case by (meson ENat gen_loc)
next
  case (Bool \<Gamma> f b)
  then show ?case by (meson EBool gen_loc)
next
  case (Var \<Gamma> x \<tau> m f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
        and x_in_env: "\<Gamma> x = Some \<tau>" by auto
  then show ?case 
  proof(cases x)
    case (V x1)
    from this and env_compat and x_in_env 
    have "x1 \<in> dom \<mu>" and eq: "x = V x1" by auto
    then obtain k where in_lookup: "\<mu> x1 = Some k" by auto
    show ?thesis
    proof(intro disjI2 exI)
      from in_lookup and eq show "< (\<mu>, \<rho>) , S x > \<rightarrow> < (\<mu>, \<rho>) , S (Loc k) >"
        by (simp add: EVar) 
    qed
  next
    case (Loc x2)
    then show ?thesis by simp
  qed
next
  case (VarDef x \<Gamma> f t)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and "finite (dom \<rho>)"
        and not_in_lookup: "x \<notin> dom \<mu>" by auto
  then obtain l where has_loc: "l \<notin> dom \<rho>" using gen_loc by blast
  show ?case
  proof(intro disjI2 exI)
    from not_in_lookup and has_loc
    show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t))) , S (Loc (l, SLoc l)) >"
      by (rule EVarDef)
  qed
next
  case (EmptyList \<Gamma> f t)
  then show ?case by simp
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and loc_typed: "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>"
        and tail_typed: "\<Delta> \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>"
        and loc_induct: "located \<L> 
                         \<or> (\<exists>\<mu>' \<rho>' \<L>''. <(\<mu>, \<rho>) , \<L>> \<rightarrow> <(\<mu>', \<rho>') , \<L>''>)"
        and tail_induct: "\<And>\<mu> \<rho>. \<lbrakk>\<Delta> \<leftrightarrow> (\<mu>, \<rho>); finite (dom \<rho>)\<rbrakk>
            \<Longrightarrow> located Tail
              \<or> (\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >)"
    by auto
   
  show ?case
  proof(cases "located \<L>")
    case True
    then have loc_l: "located \<L>" 
          and is_fin: "finite (dom \<rho>)" using ConsList.prems by auto
    then show ?thesis 
    proof(cases "located Tail")
      case True
      from this and loc_l show ?thesis by simp
    next
      case False
      from loc_l have "\<Delta> \<leftrightarrow> (\<mu>, \<rho>)" using located_env_compat ConsList by blast
      then have "\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >"
        using tail_induct ConsList False by blast
      then show ?thesis using EConsListTailCongr loc_l by blast
    qed
  next
    case False
    then have "\<exists>\<mu>' \<rho>' \<L>'. < (\<mu>, \<rho>) , \<L> > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >" using loc_induct by blast
    then show ?thesis using EConsListHeadCongr by blast
  qed
qed

fun finite_store :: "Store \<Rightarrow> bool" where
  "finite_store (\<mu>, \<rho>) = (finite (dom \<mu>) \<and> finite (dom \<rho>))"

lemma locator_preservation:
  fixes "\<Sigma>" and "\<L>" and "\<Sigma>'" and "\<L>'"
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> \<Sigma>"
      and "finite_store \<Sigma>"
    shows "finite_store \<Sigma>' 
      \<and> (\<exists>\<Gamma>' \<Delta>'. (\<Gamma>' \<leftrightarrow> \<Sigma>') \<and> (\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau> \<stileturn> \<Delta>'))"
(*TODO: We probably need some compatibility condition between \<Gamma> and \<Gamma>' and \<Delta> and \<Delta>' *)
  using assms
proof(induction arbitrary: \<Gamma> \<tau> f \<Delta>)
  case (ENat l \<rho> \<mu> n)
  let ?\<Gamma>' = "\<Gamma>(Loc (l, Amount n) \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(Loc (l, Amount n) \<mapsto> f \<tau>)"
  have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> Res (natural, Num n)))" using ENat.prems by simp
  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc (l, Amount n)) : \<tau> \<stileturn> ?\<Delta>'" by (rule Var, auto) 
  obtain \<Gamma>' and \<Delta>' 
    where "\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> Res (natural, Num n)))" 
      and "(\<Gamma>' \<turnstile>{s} f ; S (Loc (l, Amount n)) : \<tau> \<stileturn> \<Delta>')" using compat typed ..
  then show ?case using ENat.prems by auto
next
  case (EBool l \<rho> \<mu> b)
  let ?\<Gamma>' = "\<Gamma>(Loc (l, SLoc l) \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(Loc (l, SLoc l) \<mapsto> f \<tau>)"
  have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b)))" using EBool.prems by simp
  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc (l, SLoc l)) : \<tau> \<stileturn> ?\<Delta>'" by (rule Var, auto) 
  obtain \<Gamma>' and \<Delta>' 
    where "\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b)))" 
      and "(\<Gamma>' \<turnstile>{s} f ; S (Loc (l, SLoc l)) : \<tau> \<stileturn> \<Delta>')" using compat typed .. 
  then show ?case using EBool.prems by auto
next
  case (EVar \<mu> x l \<rho>)
  let ?\<Gamma>' = "\<Delta>(Loc l \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(Loc l \<mapsto> f \<tau>)"
  from EVar have "\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)" by simp (erule loc_type.cases, auto)
  then have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>)" using EVar by auto
  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'" by (meson Var fun_upd_same)
  obtain \<Gamma>' and \<Delta>' 
    where "\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>)"
      and "\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> \<Delta>'" using compat typed ..
  then show ?case using EVar.prems by auto
next
  case (EVarDef x \<mu> l \<rho> t)
  let ?\<Gamma>' = "\<Delta>(Loc (l, SLoc l) \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(Loc (l, SLoc l) \<mapsto> f \<tau>)"
  from EVarDef have "\<Delta> = \<Gamma>(V x \<mapsto> f (empty,t))" by simp (erule loc_type.cases, auto)  
  then have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t)))" using EVarDef by auto
  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc (l, SLoc l)) : \<tau> \<stileturn> ?\<Delta>'" by (meson Var fun_upd_same)
  obtain \<Gamma>' and \<Delta>'
    where "\<Gamma>' \<leftrightarrow> (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t)))"
      and "\<Gamma>' \<turnstile>{s} f ; S (Loc (l, SLoc l)) : \<tau> \<stileturn> \<Delta>'" using compat typed ..
  then show ?case using EVarDef.prems by auto
next
  case (EConsListHeadCongr \<Sigma> \<L> \<Sigma>' \<L>' \<tau>' Tail \<Gamma> \<tau>)
  then obtain \<Delta>'' where "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''" by simp (erule loc_type.cases, auto)
  then have "finite_store \<Sigma>'" and "\<exists>\<Gamma>' \<Delta>'. (\<Gamma>' \<leftrightarrow> \<Sigma>') \<and> (\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>')" 
    using EConsListHeadCongr by auto
  then obtain \<Gamma>' and \<Delta>' where "\<Gamma>' \<leftrightarrow> \<Sigma>'" and "\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'" by auto
  then show ?case 
next
  case (EConsListTailCongr \<L> \<Sigma> Tail \<Sigma>' Tail' \<tau>)
  then show ?case sorry
qed

end
