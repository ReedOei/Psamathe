theory Psamathe
  imports Main "HOL-Library.Multiset"
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = natural | boolean 
  | table "string list" "TyQuant \<times> BaseTy"
  | named string BaseTy (* TODO: Need to add modifiers *)
type_synonym Type = "TyQuant \<times> BaseTy"
datatype Mode = s | d

datatype Val = Num nat | Bool bool | Table "Val multiset"
type_synonym Resource = "BaseTy \<times> Val"
datatype Stored = V string | Loc nat

datatype Locator = N nat | B bool | S Stored
  | VDef string BaseTy ("var _ : _")
  | EmptyList Type ("[ _ ; ]")
  | ConsList Type "Locator" "Locator" ("[ _ ; _ , _ ]")
  | Copy Locator ("copy'(_')")
datatype Stmt = Flow Locator Locator (infix "\<longlonglongrightarrow>" 40)
  | Revert
datatype Prog = Prog "Stmt list"

type_synonym Env = "Stored \<rightharpoonup> Type"
type_synonym Store = "(string \<rightharpoonup> nat) \<times> (nat \<rightharpoonup> Resource)"

fun sub_store :: "Store \<Rightarrow> Store \<Rightarrow> bool" (infix "\<subseteq>\<^sub>s" 50) where
  "sub_store (\<mu>, \<rho>) (\<mu>', \<rho>') = (\<mu> \<subseteq>\<^sub>m \<mu>' \<and> \<rho> \<subseteq>\<^sub>m \<rho>')"

definition toQuant :: "nat \<Rightarrow> TyQuant" where
  "toQuant n \<equiv> (if n = 0 then empty else if n = 1 then one else nonempty)"

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

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ ; _ : _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} f ; (N n) : (toQuant(n), natural) \<stileturn> \<Gamma>"
| Bool: "\<Gamma> \<turnstile>{s} f ; (B b) : (any, boolean) \<stileturn> \<Gamma>"
| Var: "\<lbrakk> \<Gamma> (V x) = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (V x)) : \<tau> \<stileturn> (\<Gamma>(V x \<mapsto> f \<tau>))"
| Loc: "\<lbrakk> \<Gamma> (Loc l) = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (Loc l)) : \<tau> \<stileturn> (\<Gamma>(Loc l \<mapsto> f \<tau>))"
| VarDef: "\<lbrakk> V x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} f ; (var x : t) : (empty, t) \<stileturn> (\<Gamma>(V x \<mapsto> f(empty, t)))"
| EmptyList: "\<Gamma> \<turnstile>{s} f ; [ \<tau> ; ] : (empty, table [] \<tau>) \<stileturn> \<Gamma>"
| ConsList: "\<lbrakk> \<Gamma> \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta> ;
              \<Delta> \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi> \<rbrakk> 
             \<Longrightarrow> \<Gamma> \<turnstile>{s} f ; [ \<tau> ; \<L>, Tail ] : (one \<oplus> q, table [] \<tau>) \<stileturn> \<Xi>"
| Copy: "\<lbrakk> \<Gamma> \<turnstile>{s} id ; L : \<tau> \<stileturn> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{s} f ; copy(L) : demote \<tau> \<stileturn> \<Gamma>"

(* TODO: Kind of annoying to have to copy all the rules above to this... *)
(* This let's us compute the type and output environment, which is, in turn, useful for computing offsets *)
fun typecheck :: "Env \<Rightarrow> Mode \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Locator \<Rightarrow> (Type \<times> Env) option" where
  "typecheck \<Gamma> s f (N n) = Some ((toQuant n, natural), \<Gamma>)"
| "typecheck \<Gamma> s f (B b) = Some ((any, boolean), \<Gamma>)"
| "typecheck \<Gamma> m f (S x) = 
    (if (\<exists>\<tau>. \<Gamma> x = Some \<tau>) then 
      let \<tau> = (SOME \<tau>. \<Gamma> x = Some \<tau>) in Some (\<tau>, \<Gamma>(x \<mapsto> f \<tau>)) else None)"
| "typecheck \<Gamma> d f (var x : t) = 
    (if V x \<notin> dom \<Gamma> then Some ((empty, t), \<Gamma>(V x \<mapsto> f(empty, t))) else None)"
| "typecheck \<Gamma> s f [\<tau>; ] = Some ((empty, table [] \<tau>), \<Gamma>)"
| "typecheck \<Gamma> s f [\<tau>; L, Tail] =
   (case typecheck \<Gamma> s f L of
      Some (\<tau>', \<Delta>) \<Rightarrow>
        (case typecheck \<Delta> s f Tail of
          Some ((q, table [] \<tau>''), \<Xi>) \<Rightarrow> if \<tau> = \<tau>' \<and> \<tau> = \<tau>'' then Some ((one \<oplus> q, table [] \<tau>), \<Xi>) else None
          | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"
| "typecheck \<Gamma> s f copy(L) = 
    (case typecheck \<Gamma> s id L of
       Some (\<tau>, \<Gamma>') \<Rightarrow> if \<Gamma> = \<Gamma>' then Some (demote \<tau>, \<Gamma>) else None
     | _ \<Rightarrow> None)"
| "typecheck _ _ _ _ = None"

lemma typecheck_matches_loc_type:
  fixes L \<Gamma> m f \<tau> \<Delta>
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
  shows "typecheck \<Gamma> m f L = Some (\<tau>, \<Delta>)"
  using assms
    apply induction
    apply auto
    by (smt case_prod_conv demote.simps eq_id_iff option.simps(5))
(*
next
  assume "typecheck \<Gamma> m f L = Some (\<tau>, \<Delta>)"
  then show "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    apply (induction L arbitrary: \<Gamma> m f \<tau> \<Delta>)
    apply auto
  proof -
    fix n \<Gamma> m f \<tau> \<Delta>
    assume "typecheck \<Gamma> m f (N n) = Some (\<tau>, \<Delta>)"
    then show "\<Gamma> \<turnstile>{m} f ; N n : \<tau> \<stileturn> \<Delta>"
      apply (cases m)
      using Nat by auto
  next
    fix b \<Gamma> m f \<tau> \<Delta>
    assume "typecheck \<Gamma> m f (B b) = Some (\<tau>, \<Delta>)"
    then show "\<Gamma> \<turnstile>{m} f ; B b : \<tau> \<stileturn> \<Delta>"
      apply (cases m)
      using Bool by auto
  next
    fix x \<Gamma> m f \<tau> \<Delta>
    show "\<And>\<Gamma> m f a b \<Delta>.
       (if \<exists>a b. \<Gamma> x = Some (a, b) then let \<tau> = SOME \<tau>. \<Gamma> x = Some \<tau> in Some (\<tau>, \<Gamma>(x \<mapsto> f \<tau>)) else None) =
       Some ((a, b), \<Delta>) \<Longrightarrow>
       \<Gamma> \<turnstile>{m} f ; S x : (a, b) \<stileturn> \<Delta>"
      apply (cases x)
       apply (cases "\<exists>\<tau>. \<Gamma> x = Some \<tau>")
      apply auto
sorry
  next
    fix x t \<Gamma> m f \<tau> \<Delta>
    assume "typecheck \<Gamma> m f (var x : t) = Some (\<tau>, \<Delta>)" 
    then show "\<Gamma> \<turnstile>{m} f ; (var x : t) : \<tau> \<stileturn> \<Delta>"
      apply (cases m)
      apply (cases "V x \<notin> dom \<Gamma>", auto)
      by (metis Pair_inject VarDef option.discI option.inject)
  next
    fix \<tau>' \<Gamma> m f \<tau> \<Delta>
    assume "typecheck \<Gamma> m f [ \<tau>' ; ] = Some (\<tau>, \<Delta>)"
    then show "\<Gamma> \<turnstile>{m} f ; [ \<tau>' ; ] : \<tau> \<stileturn> \<Delta>"
      apply (cases m, auto)
      by (simp add: EmptyList)
  next
    fix \<tau>' L Tail \<Gamma> m f \<tau> \<Delta>
    assume "\<And>\<Gamma> m f a b \<Delta>. typecheck \<Gamma> m f L = Some ((a, b), \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; L : (a, b) \<stileturn> \<Delta>"
      and "\<And>\<Gamma> m f a b \<Delta>. typecheck \<Gamma> m f Tail = Some ((a, b), \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; Tail : (a, b) \<stileturn> \<Delta>"
      and "typecheck \<Gamma> m f [ \<tau>' ; L , Tail ] = Some (\<tau>, \<Delta>)"
    then show "\<Gamma> \<turnstile>{m} f ; [ \<tau>' ; L , Tail ] : \<tau> \<stileturn> \<Delta>"
      apply (cases m, auto)
      apply (cases "typecheck \<Gamma> s f L", auto)
    proof -
      fix \<Delta>' \<sigma>
      assume "(case typecheck \<Delta>' s f Tail of None \<Rightarrow> None
         | Some ((q, table [] \<tau>''), \<Xi>) \<Rightarrow> if \<tau>' = \<sigma> \<and> \<tau>' = \<tau>'' then Some ((one \<oplus> q, table [] \<tau>'), \<Xi>) else None
         | Some ((q, table (aa # x) \<tau>''), \<Xi>) \<Rightarrow> Map.empty x | Some ((q, named list xa), \<Xi>) \<Rightarrow> Map.empty xa
         | Some ((q, _), \<Xi>) \<Rightarrow> None) =
        Some (\<tau>, \<Delta>)"
        and "m = s" and "\<And>\<Gamma> m f a b \<Delta>. typecheck \<Gamma> m f Tail = Some ((a, b), \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; Tail : (a, b) \<stileturn> \<Delta>"
        and "typecheck \<Gamma> s f L = Some (\<sigma>, \<Delta>')"
      then show "\<Gamma> \<turnstile>{s} f ; [ \<tau>' ; L , Tail ] : \<tau> \<stileturn> \<Delta>"
        apply (cases "typecheck \<Delta>' s f Tail")
        apply auto
        sorry
    qed
  next
    fix L \<Gamma> m f a b \<Delta>
    assume "\<And>\<Gamma> m f a b \<Delta>. typecheck \<Gamma> m f L = Some ((a, b), \<Delta>) \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; L : (a, b) \<stileturn> \<Delta>"
      and "typecheck \<Gamma> m f copy(L) = Some ((a, b), \<Delta>)"
    then show "\<Gamma> \<turnstile>{m} f ; copy(L) : (a, b) \<stileturn> \<Delta>"
      apply (cases m, auto)
      apply (cases "typecheck \<Gamma> s id L", auto)
      by (metis Copy fst_conv option.distinct(1) option.inject snd_conv)
  qed
qed *)

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal natural = Num 0"
| "emptyVal boolean = Bool False"
| "emptyVal (table keys t) = Table {#}"
| "emptyVal (named name baseT) = emptyVal baseT"

fun located :: "Locator \<Rightarrow> bool" where
  "located (S (Loc _)) = True"
| "located [ \<tau> ; ] = True"
| "located [ \<tau> ; Head, Tail ] = (located Head \<and> located Tail)"
| "located copy(L) = located L"
| "located _ = False"

fun freshLoc :: "(nat \<rightharpoonup> Resource) \<Rightarrow> nat" where
  "freshLoc \<rho> = Max (dom \<rho>) + 1"

fun base_type_compat :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> bool" (infix "\<approx>" 50) where
  "base_type_compat natural natural = True"
| "base_type_compat boolean boolean = True"
| "base_type_compat (table ks1 (q1,t1)) (table ks2 (q2,t2)) = base_type_compat t1 t2"
| "base_type_compat (named name1 baseT1) (named name2 baseT2) = (name1 = name2 \<and> baseT1 = baseT2)"
| "base_type_compat _ _ = False"

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

fun deepCopy :: "(nat \<rightharpoonup> Resource) \<Rightarrow> Locator \<Rightarrow> Resource option" where
  "deepCopy \<rho> (S (Loc k)) = demoteResource (\<rho> k)"
| "deepCopy \<rho> [\<tau>; ] = Some (table [] (demote \<tau>), Table {#})"
| "deepCopy \<rho> [\<tau>; Head, Tail] = 
  (
    case (deepCopy \<rho> Head, deepCopy \<rho> Tail) of
      (Some (t1, v), Some (t2, Table vs)) \<Rightarrow> Some (t2, Table ({#v#} + vs))
    | _ \<Rightarrow> None
  )"
| "deepCopy \<rho> copy(L) = deepCopy \<rho> L"
(* Ignore everything else, we'll only call deepCopy on "located" Locators *)
| "deepCopy \<rho> _ = None"

inductive loc_eval :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> Locator \<Rightarrow> bool"
  ("< _ , _ > \<rightarrow> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (natural, Num n))), S (Loc l) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b))), S (Loc l) >"
| EVar: "\<lbrakk> \<mu> x = Some l \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), S (V x) > \<rightarrow> < (\<mu>, \<rho>), S (Loc l) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<rightarrow> < (\<mu>(x \<mapsto> l), \<rho>(l \<mapsto> (t, emptyVal t))), S (Loc l) >"
| EConsListHeadCongr: "\<lbrakk> < \<Sigma>, \<L> > \<rightarrow> < \<Sigma>', \<L>' > \<rbrakk>
                   \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<rightarrow> < \<Sigma>', [ \<tau> ; \<L>', Tail ] >"
| EConsListTailCongr: "\<lbrakk> located \<L> ; < \<Sigma>, Tail > \<rightarrow> < \<Sigma>', Tail' > \<rbrakk>
              \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<rightarrow> < \<Sigma>', [ \<tau> ; \<L>, Tail' ] >"
| ECopyCongr: "\<lbrakk> <\<Sigma>, L> \<rightarrow> <\<Sigma>', L'> \<rbrakk> \<Longrightarrow> <\<Sigma>, copy(L)> \<rightarrow> <\<Sigma>', copy(L')>"

inductive stmt_ok :: "Env \<Rightarrow> Stmt \<Rightarrow> Env \<Rightarrow> bool" ("_ \<turnstile> _ ok \<stileturn> _") where
  Flow: "\<lbrakk> \<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; Src : (q,t) \<stileturn> \<Delta>;
           \<Delta> \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (_,t) \<stileturn> \<Xi> \<rbrakk>
         \<Longrightarrow> \<Gamma> \<turnstile> (Src \<longlonglongrightarrow> Dst) ok \<stileturn> \<Xi>"
| Revert: "\<Gamma> \<turnstile> Revert ok \<stileturn> \<Gamma>"

fun typecheck_stmt :: "Env \<Rightarrow> Stmt \<Rightarrow> Env" where
  "typecheck_stmt \<Gamma> (Src \<longlonglongrightarrow> Dst) = 
    (case typecheck \<Gamma> s (\<lambda>(_,t). (empty, t)) Src of
      Some ((q,_), \<Delta>) \<Rightarrow> 
        (case typecheck \<Delta> d (\<lambda>(r,s). (r \<oplus> q, s)) Dst of 
          Some (_, \<Xi>) \<Rightarrow> \<Xi>
          | _ \<Rightarrow> \<Gamma>)
    | _ \<Rightarrow> \<Gamma>)"
| "typecheck_stmt \<Gamma> Revert = \<Gamma>"

lemma typecheck_stmt_works:
  assumes "\<Gamma> \<turnstile> Stmt ok \<stileturn> \<Delta>"
  shows "typecheck_stmt \<Gamma> Stmt = \<Delta>"
  using assms
proof(induction)
  case (Flow \<Gamma> Src q t \<Delta> Dst uu \<Xi>)
  then have "typecheck \<Gamma> s (\<lambda>(_, t). (empty, t)) Src = Some ((q, t), \<Delta>)"
        and "typecheck \<Delta> d (\<lambda>(r, s). (r \<oplus> q, s)) Dst = Some ((uu, t), \<Xi>)"
    by (auto simp: typecheck_matches_loc_type)
  then show ?case by auto
next
  case (Revert \<Gamma>)
  then show ?case by simp
qed

fun stmts_ok :: "Env \<Rightarrow> Stmt list \<Rightarrow> Env \<Rightarrow> bool" ("_ \<turnstile> _ oks \<stileturn> _") where
  "(\<Gamma> \<turnstile> [] oks \<stileturn> \<Delta>) = (\<Gamma> = \<Delta>)"
| "(\<Gamma> \<turnstile> (S1 # \<S>) oks \<stileturn> \<Xi>) = (\<exists>\<Delta>. (\<Gamma> \<turnstile> S1 ok \<stileturn> \<Delta>) \<and> (\<Delta> \<turnstile> \<S> oks \<stileturn> \<Xi>))"

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

fun less_general_quant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "less_general_quant q any = True"
| "less_general_quant one r = (r \<in> {one, nonempty})"
| "less_general_quant nonempty r = (r = nonempty)"
| "less_general_quant empty r = (r = empty)"
| "less_general_quant any r = (r = any)"

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

fun var_dom :: "Env \<Rightarrow> string set" where
  "var_dom \<Gamma> = { x . V x \<in> dom \<Gamma> }"

fun loc_dom :: "Env \<Rightarrow> nat set" where
  "loc_dom \<Gamma> = { l . Loc l \<in> dom \<Gamma> }"

fun type_less_general :: "Type option \<Rightarrow> Type option \<Rightarrow> bool" (infix "\<preceq>\<^sub>\<tau>" 50) where
  "type_less_general (Some (q,t)) (Some (r,u)) = (q \<sqsubseteq> r \<and> t = u)"
| "type_less_general None None = True"
| "type_less_general _ _ = False"

fun locations :: "Locator \<Rightarrow> nat multiset" where
  "locations (N n) = {#}"
| "locations (B b) = {#}"
| "locations (S (V x)) = {#}"
| "locations (S (Loc l)) = {#l#}"
| "locations (var x : t) = {#}"
 (* NOTE: We consider copy(L) to have no locations, because the locations won't be modified *)
| "locations (copy(L)) = locations L"
| "locations [ \<tau> ; ] = {#}"
| "locations [ \<tau> ; \<L>, Tail ] = (locations \<L> + locations Tail)"

fun wf_locator :: "Locator \<Rightarrow> bool" ("_ wf" 10) where
  "(copy(L) wf) = (L wf)"
| "([ \<tau> ; L, Tail ] wf) = ((L wf) \<and> (Tail wf) \<and> (\<not>(located L) \<longrightarrow> locations Tail = {#}))"
| "(_ wf) = True"

fun wf_stmt :: "Stmt \<Rightarrow> bool" ("_ stmt'_wf" 10) where
  "(Src \<longlonglongrightarrow> Dst stmt_wf) = ((Src wf) \<and> (Dst wf) \<and> 
    (case Src of
        copy(L) \<Rightarrow> locations Dst = {#}
      | _ \<Rightarrow> \<not>(located Src) \<longrightarrow> locations Dst = {#}))"
| "(Revert stmt_wf) = True"

fun stmt_locations :: "Stmt \<Rightarrow> nat multiset" where
  "stmt_locations (Src \<longlonglongrightarrow> Dst) = (locations Src + locations Dst)"
| "stmt_locations Revert = {#}"

inductive stmt_eval :: "Store \<Rightarrow> Stmt list \<Rightarrow> Store \<Rightarrow> Stmt list \<Rightarrow> bool"
  ("\<langle> _ , _ \<rangle> \<rightarrow> \<langle> _ , _ \<rangle>") where
  EFlowSrcCongr: "\<lbrakk> < \<Sigma>, Src > \<rightarrow> < \<Sigma>', Src' > \<rbrakk> \<Longrightarrow> \<langle> \<Sigma>, [ Src \<longlonglongrightarrow> Dst ] \<rangle> \<rightarrow> \<langle> \<Sigma>', [ Src' \<longlonglongrightarrow> Dst ] \<rangle>"
| EFlowDstCongr: "\<lbrakk> located Src ; \<not>(\<exists>L. Src = copy(L)); < \<Sigma>, Dst > \<rightarrow> < \<Sigma>', Dst' > \<rbrakk> 
                  \<Longrightarrow> \<langle> \<Sigma>, [ Src \<longlonglongrightarrow> Dst ] \<rangle> \<rightarrow> \<langle> \<Sigma>', [ Src \<longlonglongrightarrow> Dst' ] \<rangle>"
| EFlowLoc: "\<lbrakk> \<rho> l = r1; r1 -\<^sub>r r1 \<noteq> None;
               (\<rho>(l := r1 -\<^sub>r r1)) k = r2; r2 +\<^sub>r r1 \<noteq> None \<rbrakk>
             \<Longrightarrow> \<langle>(\<mu>, \<rho>), [ S (Loc l) \<longlonglongrightarrow> S (Loc k) ]\<rangle> \<rightarrow>
                 \<langle>(\<mu>, \<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1)), []\<rangle>"
| EFlowLocFail: "\<lbrakk> \<rho> l = r1; r1 -\<^sub>r r1 = None \<or> r2 +\<^sub>r r1 = None;
                   (\<rho>(l := r1 -\<^sub>r r1)) k = r2 \<rbrakk>
             \<Longrightarrow> \<langle>(\<mu>, \<rho>), [ S (Loc l) \<longlonglongrightarrow> S (Loc k) ]\<rangle> \<rightarrow> \<langle>(\<mu>, \<rho>), [ Revert ]\<rangle>"
| EFlowEmptyList: "\<lbrakk> located Dst \<rbrakk> \<Longrightarrow> \<langle>(\<mu>, \<rho>), [ [ \<tau>; ] \<longlonglongrightarrow> Dst ]\<rangle> \<rightarrow> \<langle>(\<mu>, \<rho>), []\<rangle>"
(* TODO: For this, we may ned to distinguish between located things and copy; this will also help 
         us fix copy. Located is what we need to use when something is an actual location, and 
         `evaluated` is when we stop using locator_eval (or something like that). *)
| EFlowConsList: "\<lbrakk> located Head; located Tail; located Dst \<rbrakk>
                  \<Longrightarrow> \<langle>(\<mu>, \<rho>), [ [ \<tau>; Head, Tail ] \<longlonglongrightarrow> Dst ]\<rangle> \<rightarrow> 
                      \<langle>(\<mu>, \<rho>), [ Head \<longlonglongrightarrow> Dst, Tail \<longlonglongrightarrow> Dst]\<rangle>"
| EFlowCopy: "\<lbrakk> located L; locations Dst = {#}; l \<notin> dom \<rho> \<rbrakk>
              \<Longrightarrow> \<langle>(\<mu>, \<rho>), [ copy(L) \<longlonglongrightarrow> Dst ]\<rangle> \<rightarrow> 
                  \<langle>(\<mu>, \<rho>(l := deepCopy \<rho> L)), [ S (Loc l) \<longlonglongrightarrow> Dst ]\<rangle>" 
| EStmtsCongr: "\<lbrakk> \<langle>\<Sigma>, [S1]\<rangle> \<rightarrow> \<langle>\<Sigma>', \<S>\<^sub>1'\<rangle> \<rbrakk> \<Longrightarrow> \<langle>\<Sigma>, S1 # \<S>\<^sub>2\<rangle> \<rightarrow> \<langle>\<Sigma>', \<S>\<^sub>1' @ \<S>\<^sub>2\<rangle>"

fun finite_store :: "Store \<Rightarrow> bool" where
  "finite_store (\<mu>, \<rho>) = (finite (dom \<mu>) \<and> finite (dom \<rho>))"

fun wf_stmts :: "Stmt list \<Rightarrow> bool" ("_ stmts'_wf" 10) where
  "wf_stmts [] = True"
| "wf_stmts (Stmt # Stmts) = ((Stmt stmt_wf) \<and> 
                              (\<forall>Stmt' \<in> set Stmts. (stmt_locations Stmt' = {#} \<and> (Stmt' stmt_wf))))"

fun var_ty_env :: "Env \<Rightarrow> (string \<rightharpoonup> Type)" where
  "var_ty_env \<Gamma> = (\<lambda>x. \<Gamma> (V x))"

fun loc_ty_env :: "Env \<Rightarrow> (nat \<rightharpoonup> Type)" where
  "loc_ty_env \<Gamma> = (\<lambda>l. \<Gamma> (Loc l))"

type_synonym 'a Offset = "'a \<Rightarrow> (Type \<Rightarrow> Type) list" 

definition apply_offset :: "'a Offset \<Rightarrow> 'a \<Rightarrow> Type \<Rightarrow> Type" ("_\<^sup>_[_]" 110) where
  "apply_offset \<O> l \<equiv> foldl (\<circ>) id (\<O> l)"

nonterminal offset_let

syntax
  "_offset_let" :: "['a, Type \<Rightarrow> Type] \<Rightarrow> offset_let" ("_ /@@/ _")
  "_OffsetUpd"  :: "['a Offset, offset_let] \<Rightarrow> 'a \<Rightarrow> (Type \<Rightarrow> Type) list" ("_/'(_')" [900, 0] 900)

translations
  "_OffsetUpd \<O> (_offset_let l f)" \<rightharpoonup> "\<O>(l := \<O> l @ [f])"

definition offset_comp :: "'a Offset \<Rightarrow> 'a Offset \<Rightarrow> 'a Offset" (infixl "\<circ>\<^sub>o" 65) where
  "\<O> \<circ>\<^sub>o \<P> \<equiv> (\<lambda>l. \<O> l @ \<P> l)"

lemma offset_comp_assoc: "(\<O> \<circ>\<^sub>o \<P>) \<circ>\<^sub>o \<Q> = \<O> \<circ>\<^sub>o (\<P> \<circ>\<^sub>o \<Q>)"
  by (auto simp: offset_comp_def)

lemma comp_id_nop: "foldl (\<circ>) f (replicate n id) = f"
  by (induction n, auto)

(* TODO: I feel like there should be some way to combine:
    - var_store_sync
    - env_select_var_compat
    - env_select_loc_compat
*)
definition var_store_sync :: "Env \<Rightarrow> nat Offset \<Rightarrow> (string \<rightharpoonup> nat) \<Rightarrow> bool" where
  "var_store_sync \<Gamma> \<O> \<mu> \<equiv>
      \<forall>x l \<tau>. (\<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau>) \<longrightarrow> \<Gamma> (V x) = Some (\<O>\<^sup>l[\<tau>])"

definition env_select_var_compat :: "Env \<Rightarrow> nat Offset \<Rightarrow> nat Offset \<Rightarrow> Store \<Rightarrow> bool" where
  "env_select_var_compat \<Gamma> \<O> \<P> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow>
    \<forall>x \<tau> l. \<Gamma> (V x) = Some \<tau> \<and> \<mu> x = Some l \<longrightarrow> (\<exists>\<sigma>. exactType (\<rho> l) = Some \<sigma> \<and> ((\<O> \<circ>\<^sub>o \<P>)\<^sup>l[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>)"

definition env_select_loc_compat :: "Env \<Rightarrow> nat Offset \<Rightarrow> (nat \<rightharpoonup> Resource) \<Rightarrow> bool" where
  "env_select_loc_compat \<Gamma> \<O> \<rho> \<equiv>
    \<forall>l \<tau>. \<Gamma> (Loc l) = Some \<tau> \<longrightarrow> (\<exists>\<sigma>. exactType (\<rho> l) = Some \<sigma> \<and> (\<O>\<^sup>l[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>)"

definition env_select_compat :: "Env \<Rightarrow> nat Offset \<Rightarrow> nat Offset \<Rightarrow> Store \<Rightarrow> bool" where
  "env_select_compat \<Gamma> \<O> \<P> \<Sigma> \<equiv> 
    case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> env_select_var_compat \<Gamma> \<O> \<P> \<Sigma> \<and> env_select_loc_compat \<Gamma> \<P> \<rho>"

lemma env_select_compatI[intro]:
  assumes "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
      and "env_select_loc_compat \<Gamma> \<P> \<rho>"
    shows "env_select_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
  using assms
  by (auto simp: env_select_compat_def)

lemma env_select_compatD:
  assumes "env_select_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
  shows "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" and "env_select_loc_compat \<Gamma> \<P> \<rho>"
  using assms
  by (auto simp: env_select_compat_def)

lemma env_select_compatE[elim]:
  assumes "env_select_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
      and "\<lbrakk> env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>); env_select_loc_compat \<Gamma> \<P> \<rho> \<rbrakk> \<Longrightarrow> P \<Gamma> \<O> \<P> \<mu> \<rho>"
    shows "P \<Gamma> \<O> \<P> \<mu> \<rho>"
  using assms
  by (auto simp: env_select_compat_def)

lemma env_select_var_compat_use:
  assumes "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
    and "\<Gamma> (V x) = Some \<tau>" 
    and "\<mu> x = Some l"
  obtains \<sigma> where "exactType (\<rho> l) = Some \<sigma>" and "(\<O> \<circ>\<^sub>o \<P>)\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>"
  using assms
  apply (auto simp: env_select_var_compat_def)
  by (metis old.prod.exhaust)

lemma env_select_var_compat_use_exist:
  assumes "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
    and "\<Gamma> (V x) = Some \<tau>" 
    and "\<mu> x = Some l"
  shows "\<exists>\<sigma>. exactType (\<rho> l) = Some \<sigma> \<and> ((\<O> \<circ>\<^sub>o \<P>)\<^sup>l[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>"
  using assms
  apply (auto simp: env_select_var_compat_def)
  by (metis old.prod.exhaust)

definition loc_dom_refs_compat :: "Env \<Rightarrow> (nat \<rightharpoonup> Resource) \<Rightarrow> bool" where
  "loc_dom_refs_compat \<Gamma> \<rho> \<equiv> loc_dom \<Gamma> \<subseteq> dom \<rho>"

definition compat :: "Env \<Rightarrow> nat Offset \<Rightarrow> nat Offset \<Rightarrow> Store \<Rightarrow> bool" where
  (* NOTE: Some of these are probably redundant (e.g., env_select_loc_compat probably subsumes loc_dom_refs_compat *)
  "compat \<Gamma> \<O> \<P> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> 
                        var_dom \<Gamma> = dom \<mu> \<and>
                        (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> ran \<mu>) \<and>
                        var_store_sync \<Gamma> \<O> \<mu> \<and> 
                        inj \<mu> \<and> finite (dom \<rho>) \<and>
                        env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>) \<and>             
                        env_select_loc_compat \<Gamma> \<P> \<rho> \<and>
                        (\<forall>l t v. \<rho> l = Some (t,v) \<longrightarrow> baseTypeMatches t v)"

lemma compatI[intro]:
  assumes "var_dom \<Gamma> = dom \<mu>"
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> ran \<mu>" 
    and "var_store_sync \<Gamma> \<O> \<mu>"
    and "inj \<mu>" 
    and "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
    and "finite (dom \<rho>)"
    and "env_select_loc_compat \<Gamma> \<P> \<rho>"
    and "\<forall>l t v. \<rho> l = Some (t,v) \<longrightarrow> baseTypeMatches t v"
  shows "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
  using assms
  by (simp add: compat_def)

lemma compat_same_store_upd:
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
    and "var_dom \<Gamma>' = dom \<mu>"
    and "var_store_sync \<Gamma>' \<O>' \<mu>"
    and "env_select_var_compat \<Gamma>' \<O>' \<P>' (\<mu>, \<rho>)"
    and "env_select_loc_compat \<Gamma>' \<P>' \<rho>"
  shows "compat \<Gamma>' \<O>' \<P>' (\<mu>, \<rho>)"
  using assms
  by (auto simp: compat_def)

lemma loc_dom_refs_compat_use:
  assumes "l \<notin> dom \<rho>"
      and "loc_dom_refs_compat \<Gamma> \<rho>"
    shows "l \<notin> loc_dom \<Gamma>"
  using assms
  by (auto simp: loc_dom_refs_compat_def)

lemma exactType_preserves_tyquant:
  shows "\<exists>q. exactType (Some (t, v)) = Some (q, t)"
  by (cases v, auto)

lemma in_type_env_compat:
  fixes \<Gamma> \<mu> \<rho> x \<tau>
  assumes "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" 
    and "var_dom \<Gamma> = dom \<mu>"
    and "\<Gamma> (V x) = Some \<tau>"
  obtains l where "\<mu> x = Some l"
  using assms
proof(auto)
  assume "\<Gamma> (V x) = Some \<tau>" and "{x. V x \<in> dom \<Gamma>} = dom \<mu>"
  then have "x \<in> dom \<mu>" by auto
  then obtain l where "\<mu> x = Some l" using assms
    by (auto simp: env_select_var_compat_def)
qed

definition resource_le :: "(nat \<rightharpoonup> Resource) \<Rightarrow> (nat \<rightharpoonup> Resource) \<Rightarrow> bool" (infix "\<subseteq>\<^sub>r" 50) where
  "\<rho> \<subseteq>\<^sub>r \<rho>' \<equiv> \<rho> \<subseteq>\<^sub>m \<rho>' \<and> (\<forall>n \<in> dom \<rho>' - dom \<rho>. \<exists>r. \<rho>' n = Some r)"

definition type_preserving :: "(Type \<Rightarrow> Type) \<Rightarrow> bool" where
  "type_preserving f \<equiv> (\<forall>\<tau>. (snd \<tau>) \<approx> (snd (f \<tau>))) \<and> 
                       (\<forall>\<tau> \<sigma>. \<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma> \<longrightarrow> f \<tau> \<sqsubseteq>\<^sub>\<tau> f \<sigma>)"

lemma type_preserving_works:
  fixes f q t r s
  assumes "type_preserving f" and "t \<approx> s"
  obtains q' t' where "f (q,t) = (q', t')" and "t' \<approx> s"
  using assms
  apply (auto simp: type_preserving_def)
  using base_type_compat_sym base_type_compat_trans prod.exhaust_sel by blast

lemma compat_loc_in_env:
  fixes \<Gamma> \<mu> \<rho> l
  assumes "env_select_loc_compat \<Gamma> \<P> \<rho>" and "Loc l \<in> dom \<Gamma>"
  obtains r where "\<rho> l = Some r"
  using assms
  by (metis domD env_select_loc_compat_def exactType.elims not_Some_eq)

lemma toQuant_empty[simp]: "toQuant 0 = empty"
  by (auto simp: toQuant_def)

lemma toQuant_one[simp]: "toQuant (Suc 0) = one"
  by (auto simp: toQuant_def)

lemma env_select_loc_compat_refs_compat:
  assumes "env_select_loc_compat \<Gamma> \<P> \<rho>"
  shows "loc_dom_refs_compat \<Gamma> \<rho>"
  using assms
  apply (auto simp: env_select_loc_compat_def loc_dom_refs_compat_def)
proof -
  fix x \<tau>
  assume "\<Gamma> (Loc x) = Some \<tau>"
  then have "(\<exists>aa ba. exactType (\<rho> x) = Some (aa, ba) \<and> \<P>\<^sup>x[(aa, ba)] \<sqsubseteq>\<^sub>\<tau> \<tau>)"
    by (metis (no_types, lifting) assms env_select_loc_compat_def option.distinct(1) option.inject type_less_general.elims(2) type_less_general.elims(3))
  then show "\<exists>a b. \<rho> x = Some (a,b)"
    by (cases "\<rho> x", auto)
qed

lemma compat_elim[elim]:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
  shows "var_dom \<Gamma> = dom \<mu>" 
    and "loc_dom_refs_compat \<Gamma> \<rho>"
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> ran \<mu>" 
    and "var_store_sync \<Gamma> \<O> \<mu>"
    and "inj \<mu>" 
    and "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
    and "finite (dom \<rho>)"
    and "env_select_loc_compat \<Gamma> \<P> \<rho>"
    and "\<forall>l t v. \<rho> l = Some (t,v) \<longrightarrow> baseTypeMatches t v"
  using assms
  by (auto simp: compat_def env_select_loc_compat_refs_compat)

lemma fresh_loc_not_in_env:
  fixes \<Gamma> \<mu> \<rho> l k j
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" and "l \<notin> dom \<rho>"
  shows "Loc l \<notin> dom \<Gamma>"
  using assms compat_loc_in_env
  apply auto
  using compat_elim(8)
  by (meson domI)

lemma gen_loc:
  fixes m :: "(nat, 'a) map"
  assumes is_fin: "finite (dom m)"
  obtains "l" where "l \<notin> dom m"
  using ex_new_if_finite is_fin by auto

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

lemma compat_transfer_var_sync:
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" 
      and "var_store_sync \<Gamma> \<O>' \<mu>"
      and "env_select_var_compat \<Gamma> \<O>' \<P> (\<mu>, \<rho>)"
    shows "compat \<Gamma> \<O>' \<P> (\<mu>, \<rho>)"
  using assms
  by (auto simp: compat_def var_store_sync_def)

lemma diff_in_loc_var_ty_env_same:
  assumes "\<forall>x. \<Gamma> x \<noteq> \<Gamma>' x \<longrightarrow> (\<exists>l. x = Loc l)"
  shows "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
  using assms
  by auto

fun less_eq_Type :: "Type \<Rightarrow> Type \<Rightarrow> bool" (infix "\<le>\<^sub>\<tau>" 50) where
  "less_eq_Type (q1,t1) (q2, t2) = (q1 \<le> q2)"

definition mode_compat :: "Mode \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> bool" where
  "mode_compat m f \<equiv> case m of s \<Rightarrow> \<forall>\<tau>. f \<tau> \<le>\<^sub>\<tau> \<tau> | d \<Rightarrow> \<forall>\<tau>. \<tau> \<le>\<^sub>\<tau> f \<tau>"

lemma var_store_sync_use:
  assumes "var_store_sync \<Gamma> \<O> \<mu>"
      and "\<mu> x = Some l"
      and "\<Gamma> (Loc l) = Some \<tau>"
    shows "\<Gamma> (V x) = Some (\<O>\<^sup>l[\<tau>])"
  using assms var_store_sync_def
  by blast

lemma offset_upd: "(\<O>(l @@ f))\<^sup>l[\<tau>] = (\<O>\<^sup>l[f \<tau>])"
  by (auto simp: apply_offset_def)

lemma offset_upd_dif: 
  assumes "l \<noteq> k"
  shows "(\<O>(l @@ f))\<^sup>k[\<tau>] = (\<O>\<^sup>k[\<tau>])"
  using assms
  by (auto simp: apply_offset_def)

lemma var_store_sync_add:
  assumes "var_store_sync \<Gamma> (\<O>(l @@ f)) \<mu>"
      and "\<Gamma> (Loc l) = Some \<tau>"
  shows "var_store_sync (\<Gamma>(Loc l \<mapsto> f \<tau>)) \<O> \<mu>"
  using assms
proof(cases "\<exists>x. \<mu> x = Some l")
  case True
  then obtain x where "\<mu> x = Some l" by auto
  then have "\<Gamma> (V x) = Some (\<O>\<^sup>l[f \<tau>])" using assms True
    apply (auto simp: var_store_sync_use)
    by (simp add: offset_upd)
  then show ?thesis using assms
    apply (auto simp: var_store_sync_def)
    apply (metis offset_upd old.prod.exhaust)
    by (simp add: offset_upd_dif)
next
  case False
  then show ?thesis using assms
    apply (auto simp: var_store_sync_def)
    by (simp add: offset_upd_dif)
qed

fun update_locations :: "Env \<Rightarrow> nat Offset \<Rightarrow> Env" where
  "update_locations \<Gamma> \<O> (V x) = \<Gamma> (V x)"
| "update_locations \<Gamma> \<O> (Loc l) = map_option (\<lambda>\<tau>. (\<O>\<^sup>l[\<tau>])) (\<Gamma> (Loc l))"

lemma update_locations_id: "update_locations \<Gamma> (\<lambda>l. []) = \<Gamma>"
proof(rule ext)
  fix x
  show "update_locations \<Gamma> (\<lambda>l. []) x = \<Gamma> x" 
    apply (cases x)
    by (auto simp: option.map_id apply_offset_def)
qed

lemma foldl_comp: "foldl (\<circ>) (foldl (\<circ>) id xs) ys a = foldl (\<circ>) id xs (foldl (\<circ>) id ys a)"
  apply (induction ys arbitrary: xs)
  apply simp
  by (metis comp_apply foldl_Cons foldl_Nil fun.map_id0 id_apply)

lemma apply_offset_distrib[simp]: "(\<O> \<circ>\<^sub>o \<P>)\<^sup>l[\<tau>] = (\<O>\<^sup>l[\<P>\<^sup>l[\<tau>]])"
  apply (auto simp: offset_comp_def apply_offset_def)
  by (simp add: foldl_comp)

lemma update_locations_union: 
  assumes "update_locations \<Gamma> \<O> = \<Delta>"
      and "update_locations \<Delta> \<P> = \<Xi>"
    shows "update_locations \<Gamma> (\<P> \<circ>\<^sub>o \<O>) = \<Xi>"
proof(rule ext)
  fix x
  show "update_locations \<Gamma> (\<P> \<circ>\<^sub>o \<O>) x = \<Xi> x"
  proof(cases x)
    case (V x1)
    then show ?thesis using assms by auto
  next
    case (Loc l)
    have "update_locations \<Gamma> \<O> x = \<Delta> x" 
      and "update_locations \<Delta> \<P> x = \<Xi> x" 
      using assms by auto
    then show ?thesis using assms Loc
      apply (cases "\<Gamma> (Loc l)")
      by auto
  qed
qed

lemma update_locations_step: 
  assumes "\<Gamma>(Loc l) = Some \<tau>" 
  shows "\<Gamma>(Loc l \<mapsto> f \<tau>) = update_locations \<Gamma> (\<lambda>a. if l = a then [f] else [])"
proof(rule ext)
  fix x
  show "(\<Gamma>(Loc l \<mapsto> f \<tau>)) x = update_locations \<Gamma> (\<lambda>a. if l = a then [f] else []) x" 
    using assms
    apply (cases x)
    by (auto simp: apply_offset_def option.map_id)
qed

definition empty_offset :: "'a Offset" ("0\<^sub>\<O>") where
  "empty_offset \<equiv> (\<lambda>l. [])"

lemma empty_offset_apply[simp]: "empty_offset\<^sup>l[\<tau>] = \<tau>"
  by (auto simp: empty_offset_def apply_offset_def)

lemma offset_comp_single: "\<O> \<circ>\<^sub>o (\<lambda>k. if l = k then [f] else []) = \<O>(l @@ f)"
  by (auto simp: offset_comp_def)

lemma offset_comp_empty_r[simp]: "\<O> \<circ>\<^sub>o 0\<^sub>\<O> = \<O>"
  by (auto simp: offset_comp_def empty_offset_def)

lemma offset_comp_empty_l[simp]: "0\<^sub>\<O> \<circ>\<^sub>o \<O> = \<O>"
  by (auto simp: offset_comp_def empty_offset_def)

lemma update_loc_empty[simp]: "update_locations \<Gamma> empty_offset = \<Gamma>"
  apply (auto simp: empty_offset_def)
  by (simp add: update_locations_id)

fun build_offset :: "(Type \<Rightarrow> Type) \<Rightarrow> Locator \<Rightarrow> nat Offset" where
  "build_offset _ (N _) = empty_offset"
| "build_offset _ (B _) = empty_offset"
| "build_offset _ (S (V _)) = empty_offset"
| "build_offset f (S (Loc l)) = (\<lambda>k. if l = k then [f] else [])"
| "build_offset _ (var _ : _) = empty_offset"
| "build_offset _ [\<tau>; ] = empty_offset"
| "build_offset f [\<tau>; Head, Tail] = build_offset f Tail \<circ>\<^sub>o build_offset f Head"
| "build_offset _ copy(_) = empty_offset"

lemma build_offset_id[simp]: "update_locations \<Gamma> (build_offset id L) = \<Gamma>"
  apply (induction L, auto)
proof -
  fix x
  show "update_locations \<Gamma> (build_offset (\<lambda>a. a) (S x)) = \<Gamma>"
    apply (cases x, auto)
  proof(rule ext)
    fix y
    show "\<And>x2. update_locations \<Gamma> (\<lambda>k. if x2 = k then [\<lambda>a. a] else []) y = \<Gamma> y"
      apply (cases y, auto simp: apply_offset_def)
      apply (simp add: option.map_ident)
      by (simp add: option.map_id)
  qed

  show "\<And>L1 L2.
       \<lbrakk>update_locations \<Gamma> (build_offset (\<lambda>a. a) L1) = \<Gamma>; update_locations \<Gamma> (build_offset (\<lambda>a. a) L2) = \<Gamma>\<rbrakk>
       \<Longrightarrow> update_locations \<Gamma> (build_offset (\<lambda>a. a) L2 \<circ>\<^sub>o build_offset (\<lambda>a. a) L1) = \<Gamma> "
    by (simp add: update_locations_union)
qed

lemma build_offset_apply_id[simp]: "(build_offset id L)\<^sup>l[\<tau>] = \<tau>"
  apply (induction L, auto)
proof -
  fix x
  show "build_offset (\<lambda>a. a) (S x)\<^sup>l[\<tau>] = \<tau>"
    apply (cases x, auto simp: apply_offset_def)
    by (metis apply_offset_def empty_offset_apply)
qed

lemma compat_id: "compat \<Gamma> (build_offset id L) \<P> (\<mu>, \<rho>) \<longleftrightarrow> compat \<Gamma> empty_offset \<P> (\<mu>, \<rho>)"
proof
  assume "compat \<Gamma> (build_offset id L) \<P> (\<mu>, \<rho>)"
  then show "compat \<Gamma> empty_offset \<P> (\<mu>, \<rho>)"
    apply (intro compatI)
     apply (auto simp: compat_def)
    apply (simp add: var_store_sync_def)
    using env_select_var_compat_def by auto
next
  assume "compat \<Gamma> empty_offset \<P> (\<mu>, \<rho>)"
  then show "compat \<Gamma> (build_offset id L) \<P> (\<mu>, \<rho>)"
    apply (intro compatI)
     apply (auto simp: compat_def)
    apply (simp add: var_store_sync_def)
    using env_select_var_compat_def by auto
qed

lemma [simp]: "(empty_offset(l @@ f) \<circ>\<^sub>o \<P>)\<^sup>l[\<tau>] = f(\<P>\<^sup>l[\<tau>])"
  by (simp add: offset_upd)

lemma env_select_loc_compat_upd:
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
      and "\<Gamma> (Loc l) = Some \<tau>"
      and "type_preserving f"
  shows "env_select_loc_compat (\<Gamma>(Loc l \<mapsto> f \<tau>)) (empty_offset(l @@ f) \<circ>\<^sub>o \<P>) \<rho>"
proof(unfold env_select_loc_compat_def, intro allI impI, safe)
  obtain "\<sigma>" where loc_ty: "exactType (\<rho> l) = Some \<sigma>" using assms
    apply (auto simp: compat_def env_select_loc_compat_def)
    by (metis demote.cases)

  then have "\<P>\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>" using assms
    by (metis compat_elim(8) env_select_loc_compat_def option.inject)

  then have sub_ty: "(empty_offset(l @@ f) \<circ>\<^sub>o \<P>)\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> f \<tau>" using assms
    apply (auto simp: type_preserving_def offset_upd)
    by (metis less_general_type.elims(2))

  fix k \<tau>'
  assume lookup_ty: "(\<Gamma>(Loc l \<mapsto> f \<tau>)) (Loc k) = Some \<tau>'"
  show "\<exists>\<sigma>. exactType (\<rho> k) = Some \<sigma> \<and> ((empty_offset(l @@ f) \<circ>\<^sub>o \<P>)\<^sup>k[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>'"
  proof(cases "l = k")
    case True
    then have f_ty: "f \<tau> = \<tau>'" using lookup_ty by simp
    show ?thesis
    proof(rule exI[where x = \<sigma>], intro conjI)
      show "exactType (\<rho> k) = Some \<sigma>" using True loc_ty by simp
      show "(empty_offset(l @@ f) \<circ>\<^sub>o \<P>)\<^sup>k[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>'" using True sub_ty f_ty by simp
    qed
  next
    case False
    then obtain \<pi> where "exactType (\<rho> k) = Some \<pi>" using assms lookup_ty
      by (metis compat_elim(8) env_select_loc_compat_def fun_upd_apply)
    then show ?thesis using False assms
      by (smt Stored.inject(2) apply_offset_distrib compat_elim(8) empty_offset_apply env_select_loc_compat_def fun_upd_apply lookup_ty offset_upd_dif)
  qed
qed

lemma empty_offset_insert: "(\<lambda>k. if l = k then [f] else []) = empty_offset(l @@ f)"
  by (auto simp: empty_offset_def)

lemma env_select_loc_compat_upd2:
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
      and "\<Gamma> (Loc l) = Some \<tau>"
      and "type_preserving f"
    shows "env_select_loc_compat (\<Gamma>(Loc l \<mapsto> f \<tau>)) ((\<lambda>k. if l = k then [f] else []) \<circ>\<^sub>o \<P>) \<rho>"
  using assms
  by (metis empty_offset_insert env_select_loc_compat_upd)

lemma located_env_compat:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f \<L>) \<P> (\<mu>, \<rho>)"
      and "located \<L>"
      and "type_preserving f"
    shows "compat \<Delta> \<O> (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>, \<rho>) 
          \<and> \<Delta> = update_locations \<Gamma> (build_offset f \<L>)"
  using assms
proof(induction arbitrary: \<mu> \<rho> \<O> \<P> rule: loc_type.induct)
  case (Nat \<Gamma> f n)
  then show ?case by simp
next
  case (Bool \<Gamma> f b)
  then show ?case by simp
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case by simp
next
  case (Loc \<Gamma> l \<tau> m f)
  then have l_in_dom: "Loc l \<in> dom \<Gamma>" by auto
  then have "(\<Gamma>(Loc l \<mapsto> f \<tau>)) (Loc l) = Some (f \<tau>)" by auto
  show ?case
  proof(intro conjI compatI)
    show "var_dom (\<Gamma>(Loc l \<mapsto> f \<tau>)) = dom \<mu>" using compat_elim Loc by auto
    show "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> ran \<mu>" using compat_elim Loc by auto
    show "var_store_sync (\<Gamma>(Loc l \<mapsto> f \<tau>)) \<O> \<mu>" using Loc l_in_dom
      apply (unfold compat_def, clarsimp, safe)
      by (simp add: var_store_sync_add offset_comp_single)
    show "inj \<mu>" using compat_elim Loc by auto
    show "env_select_var_compat (\<Gamma>(Loc l \<mapsto> f \<tau>)) \<O> (build_offset f (S (Loc l)) \<circ>\<^sub>o \<P>) (\<mu>, \<rho>)" 
      using Loc
      apply (unfold env_select_var_compat_def, clarsimp)     
      apply (simp add: empty_offset_insert)
    proof -
      fix x :: "char list" and a :: TyQuant and b :: BaseTy and la :: nat
      assume a1: "\<mu> x = Some la"
      assume a2: "\<Gamma> (V x) = Some (a, b)"
      assume "Psamathe.compat \<Gamma> (\<O> \<circ>\<^sub>o 0\<^sub>\<O>(l := 0\<^sub>\<O> l @ [f])) \<P> (\<mu>, \<rho>)"
      then have f3: "env_select_var_compat \<Gamma> (\<O> \<circ>\<^sub>o 0\<^sub>\<O>(l := 0\<^sub>\<O> l @ [f])) \<P> (\<mu>, \<rho>)"
        by (metis compat_elim(6))
      have "\<forall>f n fa fb p. \<exists>pa. \<forall>fc cs fd fe csa ff. (fc cs \<noteq> Some n \<or> fd (V cs) \<noteq> Some p \<or> \<not> env_select_var_compat fd fa fb (fc, f) \<or> Some pa = exactType (f n)) \<and> (fe csa \<noteq> Some n \<or> ff (V csa) \<noteq> Some p \<or> \<not> env_select_var_compat ff fa fb (fe, f) \<or> fa \<circ>\<^sub>o fb\<^sup>n[pa] \<sqsubseteq>\<^sub>\<tau> p)"
        by (metis env_select_var_compat_use)
      then obtain pp :: "(nat \<Rightarrow> (BaseTy \<times> Val) option) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> (TyQuant \<times> BaseTy \<Rightarrow> TyQuant \<times> BaseTy) list) \<Rightarrow> (nat \<Rightarrow> (TyQuant \<times> BaseTy \<Rightarrow> TyQuant \<times> BaseTy) list) \<Rightarrow> TyQuant \<times> BaseTy \<Rightarrow> TyQuant \<times> BaseTy" where
        f4: "\<And>f cs n fa p fb fc fd fe csa ff. (f cs \<noteq> Some n \<or> fa (V cs) \<noteq> Some p \<or> \<not> env_select_var_compat fa fb fc (f, fd) \<or> Some (pp fd n fb fc p) = exactType (fd n)) \<and> (fe csa \<noteq> Some n \<or> ff (V csa) \<noteq> Some p \<or> \<not> env_select_var_compat ff fb fc (fe, fd) \<or> fb \<circ>\<^sub>o fc\<^sup>n[pp fd n fb fc p] \<sqsubseteq>\<^sub>\<tau> p)"
        by (metis (no_types))
      then have f5: "\<And>f p fa fb fc. f (V x) \<noteq> Some p \<or> \<not> env_select_var_compat f fa fb (\<mu>, fc) \<or> fa \<circ>\<^sub>o fb\<^sup>la[pp fc la fa fb p] \<sqsubseteq>\<^sub>\<tau> p"
        using a1 by blast
      have "Some (pp \<rho> la (\<O> \<circ>\<^sub>o 0\<^sub>\<O>(l := 0\<^sub>\<O> l @ [f])) \<P> (a, b)) = exactType (\<rho> la)"
        using f4 f3 a2 a1 by blast
      then have "\<exists>t ba. exactType (\<rho> la) = Some (t, ba) \<and> \<O> \<circ>\<^sub>o 0\<^sub>\<O> (l := 0\<^sub>\<O> l @ [f]) \<circ>\<^sub>o \<P>\<^sup>la[(t, ba)] \<sqsubseteq>\<^sub>\<tau> (a, b)"
        using f5 f3 a2 by (metis (no_types) surj_pair)
      then show "\<exists>t ba. exactType (\<rho> la) = Some (t, ba) \<and> \<O>\<^sup>la[0\<^sub>\<O> (l := 0\<^sub>\<O> l @ [f])\<^sup>la[\<P>\<^sup>la[(t, ba)]]] \<sqsubseteq>\<^sub>\<tau> (a, b)"
        by auto
    qed
    show "finite (dom \<rho>)" using compat_elim Loc by auto
    show "env_select_loc_compat (\<Gamma>(Loc l \<mapsto> f \<tau>)) (build_offset f (S (Loc l)) \<circ>\<^sub>o \<P>) \<rho>" using Loc
      apply (unfold compat_def, clarsimp)
      by (simp add: env_select_loc_compat_upd2)
    show "\<Gamma>(Loc l \<mapsto> f \<tau>) = update_locations \<Gamma> (build_offset f (S (Loc l)))" using Loc
      apply (unfold compat_def, clarsimp)
      by (simp add: update_locations_step)
    show "\<forall>l t v. \<rho> l = Some (t,v) \<longrightarrow> baseTypeMatches t v" using Loc compat_elim by auto
  qed
next
  case (VarDef x \<Gamma> f t)
  then show ?case by simp 
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case by simp
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have "located \<L>" and "located Tail"
        and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f Tail \<circ>\<^sub>o build_offset f \<L>) \<P> (\<mu>, \<rho>)"
        apply simp  
    using ConsList.prems(2) apply auto[1]
    using ConsList.prems(1) apply auto[1]
    using ConsList
    by (simp add: offset_comp_assoc)
  then have "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset f Tail) (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>, \<rho>)" 
    and "\<Delta> = update_locations \<Gamma> (build_offset f \<L>)" 
    using ConsList by auto
  then show "compat \<Xi> \<O> (build_offset f [\<tau>; \<L>, Tail] \<circ>\<^sub>o \<P>) (\<mu>, \<rho>) 
      \<and> \<Xi> = update_locations \<Gamma> (build_offset f [\<tau>; \<L>, Tail])" 
    apply auto
    using ConsList.IH(2) ConsList.prems(3) \<open>located Tail\<close> apply auto[1]
    apply (metis offset_comp_assoc)
    by (simp add: ConsList.IH(2) ConsList.prems(3) \<open>located Tail\<close> update_locations_union)
next
  case (Copy \<Gamma> L \<tau> f)
  then show ?case by simp
qed

(* TODO: Clean up/merge this and the other version *)
lemma located_env_compat2:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f \<L>) \<P> (\<mu>, \<rho>)"
      and "located \<L>"
      and "type_preserving f"
    shows "compat \<Delta> \<O> (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>, \<rho>)" and "\<Delta> = update_locations \<Gamma> (build_offset f \<L>)"
  using assms
  using located_env_compat apply auto[1]
  using assms(1) assms(2) assms(3) assms(4) located_env_compat by auto

lemma var_store_sync_build_id:
  assumes "var_store_sync \<Gamma> \<O> \<Sigma>"
  shows "var_store_sync \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) \<Sigma>"
  using assms
  by (auto simp: var_store_sync_def)

lemma env_select_var_compat_id:
  assumes "env_select_var_compat \<Gamma> \<O> \<P> \<Sigma>"
  shows "env_select_var_compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) \<P> \<Sigma>"
  using assms
  by (auto simp: env_select_var_compat_def)

lemma var_store_sync_build_id_empty:
  assumes "var_store_sync \<Gamma> empty_offset \<Sigma>"
  shows "var_store_sync \<Gamma> (build_offset id L) \<Sigma>"
  using assms
  by (auto simp: var_store_sync_def)

lemma locator_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f \<L>) \<P> (\<mu>, \<rho>)"
      and "\<L> wf"
      and "finite (dom \<rho>)"
      and "type_preserving f"
  shows "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. <(\<mu>, \<rho>), \<L>> \<rightarrow> <(\<mu>', \<rho>'), \<L>'> )"
  using assms
proof(induction arbitrary: \<mu> \<rho> m \<O> \<P> rule: loc_type.induct)
  case (Nat \<Gamma> f n)
  then show ?case by (meson ENat gen_loc)
next
  case (Bool \<Gamma> f b)
  then show ?case by (meson EBool gen_loc)
next
  case (Var \<Gamma> x \<tau> m f)
  then obtain k where in_lookup: "\<mu> x = Some k" using Var in_type_env_compat
    by (meson compat_elim(1) compat_elim(6))
  then show ?case
  proof(intro disjI2 exI)
    from in_lookup show "< (\<mu>, \<rho>) , S (V x) > \<rightarrow> < (\<mu>, \<rho>) , S (Loc k) >" using Var
      by (simp add: EVar) 
  qed
next
  case (Loc \<Gamma> l \<tau> m f)
  then show ?case by simp
next
  case (VarDef x \<Gamma> f t)
  then have env_compat: "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" by simp
  have not_in_lookup: "x \<notin> dom \<mu>" using VarDef by (auto simp: compat_def)
  have "finite (dom \<rho>)" using VarDef by simp
  then obtain l where has_loc: "l \<notin> dom \<rho>" using gen_loc env_compat not_in_lookup by blast
  show ?case
  proof(intro disjI2 exI)
    from not_in_lookup and has_loc
    show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> l), \<rho>(l \<mapsto> (t, emptyVal t))) , S (Loc l) >"
      by (rule EVarDef)
  qed
next
  case (EmptyList \<Gamma> f t)
  then show ?case by simp
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have env_compat: "compat \<Gamma> 
                                (\<O> \<circ>\<^sub>o build_offset f Tail \<circ>\<^sub>o build_offset f \<L>)
                                \<P>
                                (\<mu>, \<rho>)"
    by (simp add: offset_comp_assoc)

  from ConsList and wf_locator.cases 
  have "\<L> wf" and "Tail wf" and "finite (dom \<rho>)" and "type_preserving f" by fastforce+

  from this and env_compat 
  have loc_induct: "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. < (\<mu>, \<rho>) , \<L> > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >)"
    and tail_induct: "\<And>\<mu>' \<rho>'. \<lbrakk>compat \<Delta> (\<O> \<circ>\<^sub>o build_offset f Tail) (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>, \<rho>)\<rbrakk>
                         \<Longrightarrow> located Tail \<or> (\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >)"
    apply (simp add: ConsList.IH(1) union_commute)
    by (simp add: ConsList.IH(2) \<open>Tail wf\<close> \<open>type_preserving f\<close> compat_elim(7) offset_comp_assoc)
   
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
      from loc_l have "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset f Tail) (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>, \<rho>)" 
        using located_env_compat ConsList env_compat by blast
      then have "\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >"
        using tail_induct ConsList False by blast
      then show ?thesis using EConsListTailCongr loc_l by blast
    qed
  next
    case False
    then have "\<exists>\<mu>' \<rho>' \<L>'. < (\<mu>, \<rho>) , \<L> > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >" using loc_induct by blast
    then show ?thesis using EConsListHeadCongr by blast
  qed
next
  case (Copy \<Gamma> L \<tau> f)
  then have "L wf" by simp

  then have "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" using Copy by simp
  then have "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) \<P> (\<mu>, \<rho>)"
    by (meson compat_elim(4) compat_elim(6) compat_transfer_var_sync env_select_var_compat_id var_store_sync_build_id)

  have "type_preserving id" by (auto simp: type_preserving_def)

  then have ih: "located L \<or> (\<exists>\<mu>' \<rho>' a. <(\<mu>, \<rho>) , L> \<rightarrow> <(\<mu>', \<rho>') , a>)"
    using Copy.IH \<open>L wf\<close> \<open>Psamathe.compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) \<P> (\<mu>, \<rho>)\<close> compat_elim(7) by blast

  obtain l where "l \<notin> dom \<rho>" using Copy.prems(3) gen_loc by auto 
    
  then show ?case
  proof(cases "located L")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using ih using ECopyCongr by blast
  qed
qed

definition offset_dom :: "'a Offset \<Rightarrow> 'a set" where
  "offset_dom \<O> \<equiv> {l. \<O> l \<noteq> []}"

lemma not_in_offset_dom_is_id:
  assumes "l \<notin> offset_dom \<O>"
  shows "apply_offset \<O> l = id"
  using assms
  by (auto simp: offset_dom_def apply_offset_def)

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

lemma add_fresh_loc:
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
      and "offset_dom \<O> \<subseteq> loc_dom \<Gamma>"
      and "offset_dom \<P> \<subseteq> loc_dom \<Gamma>"
      and "Loc l \<notin> dom \<Gamma>"
      and "l \<notin> dom \<rho>"
      and "exactType r = Some \<tau>"
      and "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>"
      and "baseTypeMatches t v"
      and "r = Some (t, v)"
    shows "compat (\<Gamma>(Loc l \<mapsto> \<sigma>)) (\<O>(l @@ f)) \<P> (\<mu>, \<rho>(l \<mapsto> (t, v)))"
proof(rule compatI)
  show "var_dom (\<Gamma>(Loc l \<mapsto> \<sigma>)) = dom \<mu>" 
    using assms compat_elim by auto

  show "\<forall>la. la \<notin> dom (\<rho>(l \<mapsto> (t, v))) \<longrightarrow> la \<notin> ran \<mu>"
    using assms compat_elim by auto

  show "var_store_sync (\<Gamma>(Loc l \<mapsto> \<sigma>)) (\<O>(l @@ f)) \<mu>"
    using assms
    apply (auto simp: compat_def var_store_sync_def)
  proof -
    fix x \<tau> k
    have "l \<notin> ran \<mu>"
      using assms(1) assms(5) compat_elim(3) by auto
    assume "\<mu> x = Some l"
    then have "l \<in> ran \<mu>" using ranI by force
    then show "\<Gamma> (V x) = Some (\<O>(l := \<O> l @ [f])\<^sup>l[\<tau>])" using \<open>l \<notin> ran \<mu>\<close>
      by simp
  next
    fix x \<tau> k
    assume "\<mu> x = Some k" and "k \<noteq> l"
    then show "\<O>\<^sup>k[\<tau>] = ((\<O>(l := \<O> l @ [f]))\<^sup>k[\<tau>])"
      by (metis offset_upd_dif)
  qed

  show "inj \<mu>" using assms compat_elim by auto

  show "env_select_var_compat (\<Gamma>(Loc l \<mapsto> \<sigma>)) (\<O>(l @@ f)) \<P> (\<mu>, \<rho>(l \<mapsto> (t, v)))"
    using assms
    apply (auto simp: env_select_var_compat_def compat_def)
    apply (meson assms(5) ranI)
    by (simp add: offset_upd_dif)

  show "finite (dom (\<rho>(l \<mapsto> (t, v))))"
    using assms compat_elim by auto

  show "env_select_loc_compat (\<Gamma>(Loc l \<mapsto> \<sigma>)) \<P> (\<rho>(l \<mapsto> (t, v)))"
    using assms
  proof(unfold env_select_loc_compat_def, intro allI impI)
    fix m \<tau>'
    assume r_ty: "exactType r = Some \<tau>" 
      and "l \<notin> dom \<rho>"
      and "Loc l \<notin> dom \<Gamma>"
      and "offset_dom \<P> \<subseteq> loc_dom \<Gamma>"
      and "(\<Gamma>(Loc l \<mapsto> \<sigma>)) (Loc m) = Some \<tau>'"
      and exact_ty_compat: "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>"
    then have k_fresh: "l \<notin> dom \<rho>" 
          and l_id_offset: "l \<notin> offset_dom \<P>" 
      by auto
    then have "l \<notin> offset_dom \<P>" using assms compat_elim(2)
      by (auto simp: loc_dom_refs_compat_def)
    then have k_not_in_offset_id: "\<forall>\<pi>. (\<P>\<^sup>l[\<pi>]) = \<pi>"
      by (simp add: l_id_offset not_in_offset_dom_is_id)
    show "\<exists>\<sigma>. exactType ((\<rho>(l \<mapsto> (t, v))) m) = Some \<sigma> \<and> (\<P>\<^sup>m[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>'"
    proof(cases "m = l")
      case True
      then have "\<tau>' = \<sigma>"  using \<open>(\<Gamma>(Loc l \<mapsto> \<sigma>)) (Loc m) = Some \<tau>'\<close> by auto
      have "\<P>\<^sup>l[\<tau>] = \<tau>" by (simp add: k_not_in_offset_id)
      then show ?thesis using r_ty True
        apply auto
        by (metis \<open>\<tau>' = \<sigma>\<close> assms(9) demote.cases exact_ty_compat)
    next
      case False
      then have m_ty: "\<Gamma> (Loc m) = Some \<tau>'" using \<open>(\<Gamma>(Loc l \<mapsto> \<sigma>)) (Loc m) = Some \<tau>'\<close> by auto
      have sel_correct: "env_select_loc_compat \<Gamma> \<P> \<rho>" using assms compat_elim by auto
      then obtain \<pi> \<pi>' where typeof_m: "exactType (\<rho> m) = Some \<pi> \<and> (\<P>\<^sup>m[\<pi>]) \<sqsubseteq>\<^sub>\<tau> \<pi>'" using m_ty
        apply (unfold env_select_loc_compat_def)
        apply auto
        by (metis demote.cases m_ty)
      then obtain r' where "\<rho> m = Some r'" using assms m_ty
        by (meson domD domI fresh_loc_not_in_env)
      then show ?thesis
        apply auto
         apply (simp add: False)
        using typeof_m apply auto
        by (metis demote.cases env_select_loc_compat_def m_ty option.inject sel_correct)
    qed
  qed
  show "\<forall>la ta va. (\<rho>(l \<mapsto> (t, v))) la = Some (ta, va) \<longrightarrow> baseTypeMatches ta va" 
    using assms compat_elim
    by auto
qed

lemma typecheck_id_env_same_source:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>" and "f = id" amd "m = s"
  shows "\<Gamma> = \<Delta>"
  using assms
  by (induction, auto)

lemma no_locations_build_offset_empty:
  assumes "locations L = {#}"
  shows "build_offset f L = 0\<^sub>\<O>"
  using assms
  apply (induction L, auto)
  by (metis build_offset.simps(3) locations.simps(4) multi_self_add_other_not_self update_locations.elims)

lemma prf_compat_not_located:
  fixes \<Gamma> m f L \<tau> \<Delta> \<Gamma>'
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
      and "L wf"
      and "locations L = {#}"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>') 
              \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' 
              \<and> loc_ty_env \<Delta>' = loc_ty_env \<Gamma>'"
  using assms
proof(induction arbitrary: \<Gamma>')
case (Nat \<Gamma> f n)
  then show ?case using loc_type.Nat by auto 
next
  case (Bool \<Gamma> f b)
  then show ?case using loc_type.Bool by auto
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case
    apply auto
    by (metis (no_types, hide_lams) Stored.distinct(1) Stored.inject(1) fun_upd_apply loc_type.Var)
next
  case (Loc \<Gamma> l \<tau> m f)
  then show ?case by auto
next
  case (VarDef x \<Gamma> f t)
  then show ?case using loc_type.VarDef
    apply auto
    by (metis (no_types, hide_lams) Stored.distinct(1) Stored.inject(1) domD fun_upd_apply old.prod.exhaust)
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case using loc_type.EmptyList by blast 
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then obtain \<Delta>' where "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" and "var_ty_env \<Delta> = var_ty_env \<Delta>'" 
    using ConsList by auto
  then obtain \<Xi>' where "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'" and "var_ty_env \<Xi> = var_ty_env \<Xi>'"
    using ConsList
    by auto
  then show ?case using ConsList loc_type.ConsList
    apply auto
    by (metis loc_type.ConsList)
next
  case (Copy \<Gamma> L \<tau> f)
  then have "L wf" by auto
  then have "(\<Gamma>' \<turnstile>{s} id ; L : \<tau> \<stileturn> \<Gamma>') \<and> var_ty_env \<Gamma> = var_ty_env \<Gamma>' \<and> loc_ty_env \<Gamma>' = loc_ty_env \<Gamma>'"
    using Copy typecheck_id_env_same_source
    by (metis locations.simps(6))
  then show ?case using loc_type.Copy by blast 
qed

lemma step_not_located:
  assumes "<\<Sigma>, L> \<rightarrow> <\<Sigma>', L'>"
  shows "\<not>(located L)"
  using assms
  by (induction, auto)

lemma head_step_wf:
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "[\<tau>; \<L>, Tail] wf"
    shows "locations Tail = {#} \<and> (Tail wf)"
  using assms
  apply auto
  by (simp add: step_not_located)

fun temp_update_env :: "Env \<Rightarrow> Env \<Rightarrow> Env" where
  "temp_update_env \<Gamma> \<Delta> (V x) = \<Delta> (V x)"
| "temp_update_env \<Gamma> \<Delta> (Loc l) = (if Loc l \<in> dom \<Gamma> then \<Gamma> (Loc l) else \<Delta> (Loc l))"

lemma update_loc_preserve_dom: "dom \<Gamma> = dom (update_locations \<Gamma> \<O>)"
proof
  show "dom \<Gamma> \<subseteq> dom (update_locations \<Gamma> \<O>)"
  proof
    fix x
    assume "x \<in> dom \<Gamma>"
    then show "x \<in> dom (update_locations \<Gamma> \<O>)"
      apply (cases x)
      by auto
  qed
  show "dom (update_locations \<Gamma> \<O>) \<subseteq> dom \<Gamma>"
  proof
    fix x
    assume "x \<in> dom (update_locations \<Gamma> \<O>)"
    then show "x \<in> dom \<Gamma>"
      apply (cases x)
      by auto
  qed
qed

lemma env_dom_eq_sub_dom_eq: "dom \<Gamma> = dom \<Delta> \<longleftrightarrow> (loc_dom \<Gamma> = loc_dom \<Delta> \<and> var_dom \<Gamma> = var_dom \<Delta>)"
proof
  assume "dom \<Gamma> = dom \<Delta>"
  then show "loc_dom \<Gamma> = loc_dom \<Delta> \<and> var_dom \<Gamma> = var_dom \<Delta>" by simp
next
  assume doms_eq: "loc_dom \<Gamma> = loc_dom \<Delta> \<and> var_dom \<Gamma> = var_dom \<Delta>"
  show "dom \<Gamma> = dom \<Delta>" 
  proof
    show "dom \<Gamma> \<subseteq> dom \<Delta>"
    proof
      fix x
      assume "x \<in> dom \<Gamma>"
      then show "x \<in> dom \<Delta>" using doms_eq
        by (cases x, auto)
    qed

    show "dom \<Delta> \<subseteq> dom \<Gamma>"
    proof
      fix x
      assume "x \<in> dom \<Delta>"
      then show "x \<in> dom \<Gamma>" using doms_eq
        by (cases x, auto)
    qed
  qed
qed

lemma temp1:
  assumes "update_locations \<Gamma> \<O> = \<Delta>" 
      and "loc_ty_env \<Delta> \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
      and "offset_dom \<O> \<subseteq> loc_dom \<Gamma>"
  shows "update_locations (temp_update_env \<Gamma> \<Delta>') \<O> = \<Delta>'"
proof(rule ext)
  fix x
  show "update_locations (temp_update_env \<Gamma> \<Delta>') \<O> x = \<Delta>' x"
    apply (cases x, simp, simp)
    using assms
    apply simp
    apply (cases "x \<in> dom \<Gamma>")
     apply simp_all
  proof -
    fix k

    show "\<lbrakk>x = Loc k; update_locations \<Gamma> \<O> = \<Delta>; (\<lambda>l. \<Delta> (Loc l)) \<subseteq>\<^sub>m (\<lambda>l. \<Delta>' (Loc l));
           offset_dom \<O> \<subseteq>  {l. Loc l \<in> dom \<Gamma>}; Loc k \<in> dom \<Gamma>\<rbrakk>
          \<Longrightarrow> map_option (apply_offset \<O> k) (\<Gamma> (Loc k)) = \<Delta>' (Loc k)"
    proof -
      assume "Loc k \<in> dom \<Gamma>"
      then obtain \<tau> where "\<Gamma> (Loc k) = Some \<tau>"
        by auto
      have "update_locations \<Gamma> \<O> (Loc k) = \<Delta> (Loc k)"
        by (simp add: assms(1))
      then obtain \<sigma> where "\<Delta> (Loc k) = Some \<sigma>"
        by (metis \<open>Loc k \<in> dom \<Gamma>\<close> domD update_loc_preserve_dom)
      then have "\<Delta>' (Loc k) = Some \<sigma>"
        by (metis (no_types, hide_lams) assms(2) insert_dom insert_iff loc_ty_env.simps map_le_def)
      then have "update_locations \<Gamma> \<O> (Loc k) = \<Delta>' (Loc k)" 
        using \<open>\<Delta> (Loc k) = Some \<sigma>\<close> \<open>update_locations \<Gamma> \<O> (Loc k) = \<Delta> (Loc k)\<close>
        by simp
      then show ?thesis by auto
    qed

    show "\<lbrakk>x = Loc k; update_locations \<Gamma> \<O> = \<Delta>; (\<lambda>l. \<Delta> (Loc l)) \<subseteq>\<^sub>m (\<lambda>l. \<Delta>' (Loc l));
           offset_dom \<O> \<subseteq> {l. Loc l \<in> dom \<Gamma>}; Loc k \<notin> dom \<Gamma>\<rbrakk>
          \<Longrightarrow> map_option (apply_offset \<O> k) (\<Delta>' (Loc k)) = \<Delta>' (Loc k)"
    proof -
      assume "offset_dom \<O> \<subseteq> {l. Loc l \<in> dom \<Gamma>}"
         and "update_locations \<Gamma> \<O> = \<Delta>"
         and "Loc k \<notin> dom \<Gamma>" 
      then have "k \<notin> offset_dom \<O>" by auto
      then show "map_option (apply_offset \<O> k) (\<Delta>' (Loc k)) = \<Delta>' (Loc k)"
        by (simp add: not_in_offset_dom_is_id option.map_id0)
    qed
  qed
qed

lemma var_store_sync_update:
  shows "var_store_sync \<Gamma> (\<P> \<circ>\<^sub>o \<O>) \<mu> \<longleftrightarrow> var_store_sync (update_locations \<Gamma> \<O>) \<P> \<mu>"
proof
  show "var_store_sync \<Gamma> (\<P> \<circ>\<^sub>o \<O>) \<mu> \<Longrightarrow> var_store_sync (update_locations \<Gamma> \<O>) \<P> \<mu>"
  apply (unfold var_store_sync_def)
  proof(intro allI, safe)
    fix x l \<tau>
    assume "\<mu> x = Some l"
      and "update_locations \<Gamma> \<O> (Loc l) = Some \<tau>"
      and "\<forall>x l \<tau>. \<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some ((\<P> \<circ>\<^sub>o \<O>)\<^sup>l[\<tau>])"
    then obtain \<sigma> where "\<Gamma> (Loc l) = Some \<sigma>"
      by auto
    then have "\<tau> = (\<O>\<^sup>l[\<sigma>])"
      using \<open>update_locations \<Gamma> \<O> (Loc l) = Some \<tau>\<close> by auto
    then show "update_locations \<Gamma> \<O> (V x) = Some (\<P>\<^sup>l[\<tau>])"
      using \<open>\<Gamma> (Loc l) = Some \<sigma>\<close> \<open>\<forall>x l \<tau>. \<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some (\<P> \<circ>\<^sub>o \<O>\<^sup>l[\<tau>])\<close> \<open>\<mu> x = Some l\<close> by fastforce
  qed

  show "var_store_sync (update_locations \<Gamma> \<O>) \<P> \<mu> \<Longrightarrow> var_store_sync \<Gamma> (\<P> \<circ>\<^sub>o \<O>) \<mu>"
    apply (unfold var_store_sync_def)
  proof(intro allI, safe)
    fix x l \<tau>
    assume "\<forall>x l \<tau>. \<mu> x = Some l \<and> update_locations \<Gamma> \<O> (Loc l) = Some \<tau> \<longrightarrow> update_locations \<Gamma> \<O> (V x) = Some (\<P>\<^sup>l[\<tau>])"
      and "\<mu> x = Some l" 
      and "\<Gamma> (Loc l) = Some \<tau>"
    then have "\<Gamma> (V x) = Some (\<P>\<^sup>l[\<O>\<^sup>l[\<tau>]])"
      by (metis option.simps(9) update_locations.simps(1) update_locations.simps(2))
    then show "\<Gamma> (V x) = Some ((\<P> \<circ>\<^sub>o \<O>)\<^sup>l[\<tau>])"
      by (metis \<open>\<Gamma> (Loc l) = Some \<tau>\<close> option.simps(9) update_locations.simps(2) update_locations_union)
  qed
qed

lemma ty_preserving_it:
  assumes "type_preserving f"
  shows "type_preserving (f^^n)"
  using assms
  apply (auto simp: type_preserving_def)
  apply (induction n)
  apply auto
  using assms base_type_compat_trans type_preserving_def apply blast
  apply (induction n, auto)
  using assms type_preserving_def by blast

lemma type_preserving_comp:
  assumes "type_preserving f" and "type_preserving g"
  shows "type_preserving (f \<circ> g)"
  using assms
  apply (auto simp: type_preserving_def)
  apply (metis base_type_compat_trans prod.collapse)
  using assms(1) type_preserving_def by blast

lemma type_preserving_id: "type_preserving id"
  by (auto simp: type_preserving_def)

lemma type_preserving_with_quant: "type_preserving (\<lambda>(_,t). (q,t))"
  using less_general_type_refl type_preserving_def by auto

lemma foldl_comp_step: "foldl (\<circ>) f fs = f \<circ> foldl (\<circ>) id fs"
proof(rule ext, simp)
  fix x
  show "foldl (\<circ>) f fs x = f (foldl (\<circ>) id fs x)"
  proof(induction fs arbitrary: f)
    case Nil
    then show ?case by auto
  next
    case (Cons a fs)
    then show ?case
      by (metis (mono_tags, hide_lams) fcomp_apply fcomp_comp foldl_Cons foldl_Nil foldl_comp id_apply)
  qed
qed

lemma type_preserving_list_comp:
  assumes "\<forall>f \<in> set fs. type_preserving f"
  shows "type_preserving (foldl (\<circ>) id fs)"
  using assms
  apply (induction fs, auto)
  apply (simp add: type_preserving_id)
  by (metis foldl_comp_step type_preserving_comp)

definition type_preserving_offset :: "'a Offset \<Rightarrow> bool" where
  "type_preserving_offset \<O> \<equiv> \<forall>f. (\<exists>l. f \<in> set (\<O> l)) \<longrightarrow> type_preserving f"

lemma type_preserving_offset_works:
  assumes "type_preserving_offset \<O>"
  shows "type_preserving (apply_offset \<O> l)"
  using assms
  apply (auto simp: type_preserving_def type_preserving_offset_def apply_offset_def)
  using type_preserving_def type_preserving_list_comp apply force
  by (meson assms less_general_type.simps type_preserving_def type_preserving_list_comp type_preserving_offset_def)

lemma env_select_loc_compat_use:
  assumes "env_select_loc_compat \<Gamma> \<O> \<rho>"
      and "\<Gamma> (Loc l) = Some \<tau>"
    obtains \<sigma> where "exactType (\<rho> l) = Some \<sigma>" and "\<O>\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>"
  using assms
  apply (auto simp: env_select_loc_compat_def)
  using assms(1) env_select_loc_compat_def that by blast

lemma type_preserving_offset_comp:
  assumes "type_preserving_offset \<O>"
    and "type_preserving_offset \<P>"
  shows "type_preserving_offset (\<O> \<circ>\<^sub>o \<P>)"
  using assms
  by (auto simp: type_preserving_offset_def offset_comp_def)

lemma update_loc_env_select_loc_compat_spec:
  assumes "env_select_loc_compat \<Delta>' (\<O> \<circ>\<^sub>o \<Q>) \<rho>"
    and "update_locations (temp_update_env \<Gamma> \<Delta>') \<O> = \<Delta>'"
    and "env_select_loc_compat \<Gamma> \<Q> \<rho>'"
    and "\<rho>' \<subseteq>\<^sub>m \<rho>"
    and "type_preserving_offset \<O>"
    and "type_preserving_offset \<Q>"
    and "offset_dom \<O> \<subseteq> loc_dom \<Gamma>"
  shows "env_select_loc_compat (temp_update_env \<Gamma> \<Delta>') \<Q> \<rho>"
proof(unfold env_select_loc_compat_def, intro impI allI)
  fix l \<tau>
  assume "temp_update_env \<Gamma> \<Delta>' (Loc l) = Some \<tau>"
  then have "update_locations (temp_update_env \<Gamma> \<Delta>') \<O> (Loc l) = Some (\<O>\<^sup>l[\<tau>])" by simp
  show "\<exists>\<sigma>. exactType (\<rho> l) = Some \<sigma> \<and> (\<Q>\<^sup>l[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>"
  proof(cases "Loc l \<in> dom \<Gamma>")
    case True
    then have "temp_update_env \<Gamma> \<Delta>' (Loc l) = \<Gamma> (Loc l)" by simp
    then show ?thesis
      by (metis (full_types) \<open>temp_update_env \<Gamma> \<Delta>' (Loc l) = Some \<tau>\<close> assms(3) assms(4) compat_loc_in_env domI env_select_loc_compat_def map_le_def)
  next
    case False
    then have "l \<notin> loc_dom \<Gamma>" by auto
    then have "apply_offset \<O> l = id"
      by (meson assms(7) not_in_offset_dom_is_id subset_eq)
    obtain \<sigma> 
      where l_ty: "exactType (\<rho> l) = Some \<sigma>" 
        and "(\<O> \<circ>\<^sub>o \<Q>)\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> (\<O>\<^sup>l[\<tau>])"
      by (metis \<open>update_locations (temp_update_env \<Gamma> \<Delta>') \<O> (Loc l) = Some (\<O>\<^sup>l[\<tau>])\<close> assms(1) assms(2) env_select_loc_compat_def)
    then have offset_ty_lt: "\<Q>\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>"
      by (simp add: \<open>apply_offset \<O> l = id\<close>)
    have "type_preserving (apply_offset \<O> l)"
      using assms type_preserving_offset_works by auto
    then show ?thesis
    proof(intro exI conjI)
      show "exactType (\<rho> l) = Some \<sigma>" using l_ty by simp
      show "\<Q>\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>" using offset_ty_lt by simp
    qed
  qed
qed

lemma temp2:
  assumes "compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>)"
      and "type_preserving_offset \<O>"
      and "type_preserving_offset \<Q>"
      and "offset_dom \<O> \<subseteq> loc_dom \<Gamma>'"
      and "\<Gamma> = temp_update_env \<Gamma>' \<Delta>'"
      and "update_locations \<Gamma> \<O> = \<Delta>'"
      and "env_select_loc_compat \<Gamma>' \<Q> \<rho>'"
      and "\<rho>' \<subseteq>\<^sub>m \<rho>"
    shows "compat \<Gamma> (\<P> \<circ>\<^sub>o \<O>) \<Q> (\<mu>, \<rho>)"
  using assms
proof(intro compatI)
  show "\<lbrakk>compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>)\<rbrakk> \<Longrightarrow> var_dom \<Gamma> = dom \<mu>"
    apply (unfold compat_def)
    apply simp
    using update_loc_preserve_dom
    by force

  show "compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>) \<Longrightarrow> \<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> ran \<mu>"
    by (auto simp: compat_def)

  show "\<lbrakk>compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>)\<rbrakk> \<Longrightarrow> var_store_sync \<Gamma> (\<P> \<circ>\<^sub>o \<O>) \<mu>"
    by (simp add: compat_elim(4) var_store_sync_update)

  show "compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>) \<Longrightarrow> inj \<mu>"
    by (simp add: compat_elim(5))

  show "\<lbrakk>compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>); type_preserving_offset \<O>;
     type_preserving_offset \<Q>\<rbrakk> \<Longrightarrow> env_select_var_compat \<Gamma> (\<P> \<circ>\<^sub>o \<O>) \<Q> (\<mu>, \<rho>)"
    by (auto simp: env_select_var_compat_def compat_def)

  show "compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>) \<Longrightarrow> finite (dom \<rho>)"
    by (auto simp: compat_def)

  show "\<lbrakk>compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>); offset_dom \<O> \<subseteq> loc_dom \<Gamma>';
         type_preserving_offset \<O>; type_preserving_offset \<Q>; \<Gamma> = temp_update_env \<Gamma>' \<Delta>';
         env_select_loc_compat \<Gamma>' \<Q> \<rho>'; \<rho>' \<subseteq>\<^sub>m \<rho>\<rbrakk>
        \<Longrightarrow> env_select_loc_compat \<Gamma> \<Q> \<rho>"
    apply simp
    apply (rule update_loc_env_select_loc_compat_spec[where \<O> = \<O>])
    using assms(6) by auto

  show "compat (update_locations \<Gamma> \<O>) \<P> (\<O> \<circ>\<^sub>o \<Q>) (\<mu>, \<rho>)
    \<Longrightarrow> \<forall>l t v. \<rho> l = Some (t, v) \<longrightarrow> baseTypeMatches t v"
    using compat_elim by auto
qed

lemma located_dom_const:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "located L"
    shows "dom (loc_ty_env \<Gamma>) = dom (loc_ty_env \<Delta>)"
  using assms
proof(induction)
case (Nat \<Gamma> f n)
  then show ?case by simp
next
  case (Bool \<Gamma> f b)
  then show ?case  by simp
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case by simp
next
  case (Loc \<Gamma> l \<tau> m f)
  then show ?case
    apply auto
    by (metis demote.cases)
next
  case (VarDef x \<Gamma> f t)
  then show ?case by simp
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case by simp
next
case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then show ?case by simp
next
  case (Copy \<Gamma> L \<tau> f)
  then show ?case by simp
qed

lemma located_var_ignore:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    and "located L"
    and "loc_ty_env \<Delta> \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
  shows "(temp_update_env \<Gamma> \<Delta>') \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>'"
  using assms
proof(induction arbitrary: \<Delta>')
case (Nat \<Gamma> f n)
  then show ?case by simp
next
  case (Bool \<Gamma> f b)
  then show ?case by simp
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case by simp
next
  case (Loc \<Gamma> l \<tau> m f)

  then have "temp_update_env \<Gamma> \<Delta>' (Loc l) = Some \<tau>"
    by (simp add: domI)

  have "(temp_update_env \<Gamma> \<Delta>')(Loc l \<mapsto> f \<tau>) = \<Delta>'"
  proof(rule ext)
    fix x
    show "(temp_update_env \<Gamma> \<Delta>'(Loc l \<mapsto> f \<tau>)) x = \<Delta>' x" using Loc
      apply (cases x)
      apply (auto simp: map_le_def)
      apply force
      by force
  qed

  then show ?case using Loc loc_type.Loc
    by (metis \<open>temp_update_env \<Gamma> \<Delta>' (Loc l) = Some \<tau>\<close>)
next
  case (VarDef x \<Gamma> f t)
  then show ?case by simp
next
  case (EmptyList \<Gamma> f \<tau>)

  have "temp_update_env \<Gamma> \<Delta>' = \<Delta>'"
  proof(rule ext)
    fix y
    show "temp_update_env \<Gamma> \<Delta>' y = \<Delta>' y" using EmptyList
      apply (cases y)
      by (auto simp: map_le_def)
  qed

  then show ?case
    by (simp add: loc_type.EmptyList)
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)

  then have tail_ty: "(temp_update_env \<Delta> \<Delta>') \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Delta>'"
    by simp

  then have sub: "loc_ty_env \<Delta> \<subseteq>\<^sub>m loc_ty_env (temp_update_env \<Delta> \<Delta>')"
    apply auto
    using map_le_def by fastforce

  then have head_ty: "(temp_update_env \<Gamma> (temp_update_env \<Delta> \<Delta>')) \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> (temp_update_env \<Delta> \<Delta>')"
    using ConsList by simp

  have "temp_update_env \<Gamma> (temp_update_env \<Delta> \<Delta>') = temp_update_env \<Gamma> \<Delta>'"
  proof(rule ext)
    fix x
    show "temp_update_env \<Gamma> (temp_update_env \<Delta> \<Delta>') x = temp_update_env \<Gamma> \<Delta>' x"
      apply (cases x)
       apply simp
      using ConsList sub located_dom_const
      apply (auto simp: map_le_def)
      by (metis (mono_tags) demote.cases domD domI)
  qed

  then show ?case using head_ty tail_ty loc_type.ConsList by simp
next
  case (Copy \<Gamma> L \<tau> f)
  then show ?case
    by (metis loc_type.Copy located.simps(4) typecheck_id_env_same_source)
qed

lemma offset_dom_empty_is_empty[simp]: "offset_dom empty_offset = {}"
  by (auto simp: empty_offset_def offset_dom_def apply_offset_def)

lemma located_locations_in_dom:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "located L"
    shows "set_mset (locations L) \<subseteq> loc_dom \<Gamma>"
  using assms
  apply (induction, auto)
  by (smt demote.cases domD domI loc_ty_env.simps located_dom_const mem_Collect_eq subset_iff)

lemma offset_member_distrib: 
  assumes "f \<in> set ((\<P> \<circ>\<^sub>o \<O>) l)"
  shows "f \<in> set (\<P> l) \<or> f \<in> set (\<O> l)"
  using assms
  by (auto simp: offset_comp_def)

lemma offset_dom_member_distrib:
  assumes "l \<in> offset_dom (\<P> \<circ>\<^sub>o \<O>)"  
  shows "l \<in> offset_dom \<P> \<or> l \<in> offset_dom \<O>"
  using assms
  by (auto simp: offset_dom_def offset_comp_def)

lemma [simp]: "dom (loc_ty_env \<Gamma>) = loc_dom \<Gamma>"
  by auto

lemma type_check_loc_dom_same:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
  shows "loc_dom \<Gamma> = loc_dom \<Delta>"
  using assms
  apply (induction, auto)
  by metis

lemma located_locations_in_offset_dom:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    shows "offset_dom (build_offset f L) \<subseteq> loc_dom \<Gamma>"
  using assms
  apply (induction, auto)
  apply (smt mem_Collect_eq offset_dom_def)
  apply (drule offset_dom_member_distrib)
  apply auto
  by (metis demote.cases domD loc_dom.simps mem_Collect_eq subset_iff type_check_loc_dom_same)

lemma empty_offset_type_preserving: "type_preserving_offset empty_offset"
  by (auto simp: type_preserving_offset_def empty_offset_def)

lemma type_preserving_build:
  assumes "type_preserving f"
  shows "type_preserving_offset (build_offset f L)"
  using assms
  apply (induction L, auto simp: empty_offset_type_preserving)
proof -
  fix x
  show "type_preserving f \<Longrightarrow> type_preserving_offset (build_offset f (S x))"
    by (cases x, auto simp: empty_offset_type_preserving type_preserving_offset_def empty_offset_def)
next
  show "\<And>L1 L2.
       \<lbrakk>type_preserving_offset (build_offset f L1); type_preserving_offset (build_offset f L2); type_preserving f\<rbrakk>
       \<Longrightarrow> type_preserving_offset (build_offset f L2 \<circ>\<^sub>o build_offset f L1)"
    apply (auto simp: type_preserving_offset_def)
    by (meson offset_member_distrib)
qed

lemma build_offset_no_locs: 
  assumes "locations L = {#}"
  shows "build_offset f L = empty_offset"
  using assms
  apply (induction L, auto)
proof -
  fix x
  show "\<lbrakk>locations (S x) = {#}; locations L = {#}\<rbrakk> \<Longrightarrow> build_offset f (S x) = empty_offset"
    by (cases x, auto)
qed

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

lemma demoteResource_works: "exactType (demoteResource r) = map_option demote (exactType r)"
proof(cases r)
  case (Some x1)
  obtain t v where "x1 = (t,v)" by (cases x1)
  then show ?thesis using Some by (cases v, auto)
next
  case None
  then show ?thesis by simp
qed

lemma demoteBaseType_idem[simp]: "demote\<^sub>* (demote\<^sub>* t) = demote\<^sub>* t"
  by (induction t, auto)

lemma demote_idem[simp]: "demote (demote \<tau>) = demote \<tau>"
  by (cases \<tau>, auto)

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

lemma store_matches_deepCopy_matches:
  assumes store_ok: "\<forall>l t v. \<rho> l = Some (t, v) \<longrightarrow> baseTypeMatches t v"
    and "deepCopy \<rho> L \<noteq> None"
  shows "\<exists>t v. deepCopy \<rho> L = Some (t,v) \<and> baseTypeMatches t v"
  using assms
  apply (induction L, auto)
proof -
  fix x t v
  assume x_ty: "deepCopy \<rho> (S x) = Some (t, v)"
  then show "baseTypeMatches t v" 
    using store_ok
    apply (cases x, auto)
  proof -
    fix k
    assume "x = Loc k" and demoted: "demoteResource (\<rho> k) = Some (t, v)"
    then show "baseTypeMatches t v"
      apply (cases "\<rho> k", auto)
    proof(cases "\<rho> k")
      case None
      then show ?thesis using demoted by auto 
    next
      case (Some a)
      then obtain t' v' where component: "\<rho> k = Some (t', v')"
        by (cases a, auto)
      then have "baseTypeMatches t' v'"  using store_ok by auto
      then show ?thesis
        apply (rule demoteResource_matches)
        using demoted component by auto
    qed
  qed                                 
next
  fix L1 L2 t v
  assume "(case deepCopy \<rho> L1 of None \<Rightarrow> None
         | Some (t1, v) \<Rightarrow>
             case deepCopy \<rho> L2 of None \<Rightarrow> None | Some (t2, Num x) \<Rightarrow> Map.empty x | Some (t2, Bool x) \<Rightarrow> Map.empty x
             | Some (t2, Table vs) \<Rightarrow> Some (t2, Table ({#v#} + vs))) =
        Some (t, v)"
  then obtain t1 ve vs
    where l1_copy: "deepCopy \<rho> L1 = Some (t1, ve)" 
      and l2_copy: "deepCopy \<rho> L2 = Some (t, Table vs)"
      and v_eq: "v = Table ({#ve#} + vs)"
    apply (cases "deepCopy \<rho> L1", cases "deepCopy \<rho> L2", auto)
    apply (cases "deepCopy \<rho> L2", auto)
  proof -
    fix a b aa ba
    assume "deepCopy \<rho> L1 = Some (a, b)" and "deepCopy \<rho> L2 = Some (aa, ba)"
      and "(case ba of Num x \<Rightarrow> Map.empty x | Bool x \<Rightarrow> Map.empty x | Table vs \<Rightarrow> Some (aa, Table (add_mset b vs))) =
        Some (t, v)"
      and "\<And>t1 ve vs. \<lbrakk>a = t1 \<and> b = ve; aa = t \<and> ba = Table vs; v = Table (add_mset ve vs)\<rbrakk> \<Longrightarrow> thesis"
    then show thesis by (cases ba, auto)
  qed
  assume "\<exists>a b. deepCopy \<rho> L1 = Some (a, b) \<Longrightarrow> \<exists>t v. deepCopy \<rho> L1 = Some (t, v) \<and> baseTypeMatches t v"
     and "\<exists>a b. deepCopy \<rho> L2 = Some (a, b) \<Longrightarrow> \<exists>t v. deepCopy \<rho> L2 = Some (t, v) \<and> baseTypeMatches t v"
  then have "deepCopy \<rho> L2 = Some (t, Table vs)" and "baseTypeMatches t (Table vs)"
        and "deepCopy \<rho> L1 = Some (t1, ve)" and "baseTypeMatches t1 ve"
    by (auto simp: l1_copy l2_copy)
  then show "baseTypeMatches t v"
    apply (simp only: v_eq)
    apply (rule baseTypeMatches_table_prepend)
    by auto
qed

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

lemma deepCopy_makes_demoted:
  assumes "\<Gamma> \<turnstile>{s} f ; L : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> 0\<^sub>\<O> 0\<^sub>\<O> (\<mu>, \<rho>)"
      and "located L"
      and "f = id" (* TODO: Not sure why I can't just put this directly in the first assumption... *) 
  shows "\<exists>\<sigma>. exactType (deepCopy \<rho> L) = Some \<sigma> \<and> \<sigma> \<sqsubseteq>\<^sub>\<tau> demote \<tau>"
  using assms
proof(induction arbitrary: \<mu> \<rho> rule: loc_type.induct)
case (Nat \<Gamma> f n)
  then show ?case by simp
next
  case (Bool \<Gamma> f b)
  then show ?case by simp
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case by simp
next
  case (Loc \<Gamma> l \<tau> m f)
  then obtain \<tau>' where "exactType (\<rho> l) = Some \<tau>'" and "\<tau>' \<sqsubseteq>\<^sub>\<tau> \<tau>"
    by (metis compat_elim(8) empty_offset_apply env_select_loc_compat_def)
  show ?case
  proof(intro exI[where x = "demote \<tau>'"] conjI)
    show "exactType (deepCopy \<rho> (S (Loc l))) = Some (demote \<tau>')"
      apply (auto simp: demoteResource_works)
      by (metis \<open>exactType (\<rho> l) = Some \<tau>'\<close> demote.elims)
    show "demote \<tau>' \<sqsubseteq>\<^sub>\<tau> demote \<tau>"
      by (simp add: \<open>\<tau>' \<sqsubseteq>\<^sub>\<tau> \<tau>\<close> demote_lt)
  qed
next
  case (VarDef x \<Gamma> f t)
  then show ?case by simp
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case by auto
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have "located \<L>" and "located Tail" using located.cases by auto
  then obtain \<sigma> 
    where head_ty: "exactType (deepCopy \<rho> \<L>) = Some \<sigma>" and "\<sigma> \<sqsubseteq>\<^sub>\<tau> demote \<tau>"
    using ConsList by blast
  obtain qe1 te1 where "\<tau> = (qe1,te1)" by (cases \<tau>)
  then obtain qe' te' where "\<sigma> = (qe',te')" and "te' \<approx> demote\<^sub>* te1"
    using ConsList
    apply (cases \<sigma>)
    using \<open>\<sigma> \<sqsubseteq>\<^sub>\<tau> demote \<tau>\<close> by auto
  then obtain v where head_copy: "deepCopy \<rho> \<L> = Some (te', v)"
    using exactType_has_same_base_type head_ty by blast
  then have "baseTypeMatches te' v"
    by (metis ConsList.prems(1) Pair_inject compat_elim(9) option.discI option.inject store_matches_deepCopy_matches)
  obtain \<pi>
    where tail_ty: "exactType (deepCopy \<rho> Tail) = Some \<pi>" and "\<pi> \<sqsubseteq>\<^sub>\<tau> demote (q, table [] \<tau>)"
    using ConsList \<open>located Tail\<close> typecheck_id_env_same_source by blast
  then obtain q' t' where "\<pi> = (q', t')" and "q' \<sqsubseteq> q" and "t' \<approx> demote\<^sub>* (table [] \<tau>)"
    by (metis demote.cases demote.simps less_general_type.simps)
  then obtain vs where copy: "deepCopy \<rho> Tail = Some (t', vs)"
    using tail_ty exactType_has_same_base_type by blast
  then have "baseTypeMatches t' vs" using assms
    by (metis ConsList.prems(1) Pair_inject compat_elim(9) option.discI option.inject store_matches_deepCopy_matches)
  (* TODO: Ugh naming *)
  obtain ks qe2 te2 where "t' = table ks (qe2,te2)" and "te2 \<approx> demote\<^sub>* te1" 
    using \<open>t' \<approx> demote\<^sub>* (table [] \<tau>)\<close> \<open>\<tau> = (qe1,te1)\<close>
    by (cases t', auto)
  then obtain elems where "vs = Table elems"
    using \<open>baseTypeMatches t' vs\<close> baseTypeMatches.elims(2) by blast
  then have simp_copy: "deepCopy \<rho> Tail = Some (t', Table elems)"
    by (simp add: copy)
  then have "toQuant (size elems) \<sqsubseteq> q" using \<open>q' \<sqsubseteq> q\<close>
    using \<open>\<pi> = (q', t')\<close> exactType_table_len tail_ty by auto
  then show ?case 
    using ConsList copy \<open>t' \<approx> demote\<^sub>* (table [] \<tau>)\<close> simp_copy head_copy
    apply auto
    apply (simp only: Suc_eq_plus1_left)
    by (metis addQuant.simps(3) approx_quant_add_lt less_general_quant.simps(8) quant_add_comm quant_add_lt_left toQuant_def zero_neq_one)
next
  case (Copy \<Gamma> L \<tau> f)
  then have "located L" using located.cases by simp
  then show ?case using Copy by auto
qed

lemma deepCopy_baseTypeMatches:
  assumes "\<Gamma> \<turnstile>{s} f ; L : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> 0\<^sub>\<O> 0\<^sub>\<O> (\<mu>, \<rho>)"
      and "located L"
      and "f = id"
    shows "\<exists>t v. deepCopy \<rho> L = Some (t, v) \<and> baseTypeMatches t v"
  apply (rule store_matches_deepCopy_matches)
  using assms(2) compat_elim(9) apply auto[1]
  using assms apply (induction)
  apply auto
proof -
  fix l \<tau> \<Gamma>
  assume "\<Gamma> (Loc l) = Some \<tau>" and "compat \<Gamma> 0\<^sub>\<O> 0\<^sub>\<O> (\<mu>, \<rho>)"
  then have "\<rho> l \<noteq> None"
    using compat_elim(8) compat_loc_in_env by fastforce
  then show "\<exists>a b. demoteResource (\<rho> l) = Some (a, b)"
    by (meson demoteResource.elims)
next
  fix \<Gamma> f \<L> a b \<Delta> Tail q \<Xi> te ve

  assume "\<Gamma> \<turnstile>{s} id ; \<L> : (a, b) \<stileturn> \<Delta>"
  then have "\<Gamma> = \<Delta>"
    using typecheck_id_env_same_source by auto

  assume "compat \<Gamma> 0\<^sub>\<O> 0\<^sub>\<O> (\<mu>, \<rho>)"
  then have delta_compat: "compat \<Delta> 0\<^sub>\<O> 0\<^sub>\<O> (\<mu>, \<rho>)" using \<open>\<Gamma> = \<Delta>\<close> by simp

  assume "compat \<Delta> 0\<^sub>\<O> 0\<^sub>\<O> (\<mu>, \<rho>) \<Longrightarrow> \<exists>a b. deepCopy \<rho> Tail = Some (a, b)"
  then have "\<exists>t v. deepCopy \<rho> Tail = Some (t,v) \<and> baseTypeMatches t v"
    using compat_elim(9) delta_compat store_matches_deepCopy_matches by auto
  then obtain t v where tail_res: "deepCopy \<rho> Tail = Some (t, v)" and "baseTypeMatches t v"
    by auto

  assume "located Tail"
  assume "\<Delta> \<turnstile>{s} id ; Tail : (q, table [] (a, b)) \<stileturn> \<Xi>"
  then have "\<exists>\<sigma>. exactType (deepCopy \<rho> Tail) = Some \<sigma> \<and> \<sigma> \<sqsubseteq>\<^sub>\<tau> demote (q, table [] (a, b))"
    apply (rule deepCopy_makes_demoted)
    using delta_compat apply auto
    by (simp add: \<open>located Tail\<close>)
  then obtain q' t' where "exactType (deepCopy \<rho> Tail) = Some (q', t')" and "(q',t') \<sqsubseteq>\<^sub>\<tau> demote (q, table [] (a, b))"
    by auto

  then obtain ks qe2 te2 where "t' = table ks (qe2,te2)"
    by (cases t', auto)
    
  then obtain vs where "v = Table vs"
    using tail_res
    by (metis Val.exhaust \<open>baseTypeMatches t v\<close> \<open>exactType (deepCopy \<rho> Tail) = Some (q', t')\<close> baseTypeMatches.simps(10) baseTypeMatches.simps(7) exactType_preserves_tyquant option.inject prod.inject)

  assume "deepCopy \<rho> \<L> = Some (te, ve)"
  then show "\<exists>a b. (case deepCopy \<rho> Tail of None \<Rightarrow> None | Some (t2, Num x) \<Rightarrow> Map.empty x
                  | Some (t2, Bool x) \<Rightarrow> Map.empty x | Some (t2, Table vs) \<Rightarrow> Some (t2, Table ({#ve#} + vs))) =
                 Some (a, b)"
    by (simp add: \<open>v = Table vs\<close> tail_res)
qed

lemma in_var_lookup_in_store:
  assumes "\<mu> x = Some l"
    and "\<forall>k. k \<notin> dom \<rho> \<longrightarrow> k \<notin> ran \<mu>"
  shows "l \<in> dom \<rho>"
  using assms
  by (meson ranI)

lemma loc_dom_refs_compat_upd:
  assumes "loc_dom_refs_compat \<Gamma> \<rho>" 
      and "\<rho> l = Some r"
    shows "loc_dom_refs_compat (\<Gamma>(V x \<mapsto> \<sigma>, Loc l \<mapsto> \<tau>)) \<rho>"
  using assms
  by (auto simp: loc_dom_refs_compat_def)

lemma not_in_dom_compat:
  assumes "compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" and "l \<notin> dom \<rho>"
  shows "Loc l \<notin> dom \<Gamma>"
  using assms
  by (auto simp: fresh_loc_not_in_env)

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

lemma env_select_var_compat_insert_loc:
  assumes compat: "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)"
  shows "env_select_var_compat (\<Gamma>(Loc l \<mapsto> \<tau>)) \<O> \<P> (\<mu>, \<rho>)"
  using assms
  by (auto simp: env_select_var_compat_def)

lemma env_select_var_compat_insert_var:
  assumes compat: "compat \<Gamma> empty_offset \<P> (\<mu>, \<rho>)"
    and "type_preserving f"
    and "V x \<notin> dom \<Gamma>" and "x \<notin> dom \<mu>" and "l \<notin> dom \<rho>"
    (* TODO: Should be able to get rid of this assumption somehow (maybe should just assume full compat? *)
    and "l \<notin> offset_dom \<P>"
  shows "env_select_var_compat (\<Gamma>(V x \<mapsto> f (empty, t))) 
                               (empty_offset(l @@ f))
                               \<P>
                               (\<mu>(x \<mapsto> l), \<rho>(l \<mapsto> (t, emptyVal t)))"
proof(unfold env_select_var_compat_def, safe)
  fix y \<tau> k
  assume "(\<Gamma>(V x \<mapsto> f (empty, t))) (V y) = Some \<tau>" 
     and "(\<mu>(x \<mapsto> l)) y = Some k"
  show "\<exists>\<sigma>. exactType ((\<rho>(l \<mapsto> (t, emptyVal t))) k) = Some \<sigma> \<and>
               0\<^sub>\<O>(l := 0\<^sub>\<O> l @ [f]) \<circ>\<^sub>o \<P>\<^sup>k[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>"
  proof(cases "x = y")
    case True
    then have "apply_offset \<P> l = id" and "k = l"
      using assms
      apply (simp add: not_in_offset_dom_is_id)
      using  \<open>(\<mu>(x \<mapsto> l)) y = Some k\<close> True
      by simp
    then show ?thesis
      using assms True
      apply simp
      by (metis \<open>(\<Gamma>(V x \<mapsto> f (empty, t))) (V y) = Some \<tau>\<close> empty_offset_apply fun_upd_same less_general_type_refl offset_upd option.inject)
  next
    case False
    then show ?thesis using assms \<open>(\<mu>(x \<mapsto> l)) y = Some k\<close>
      apply auto
      apply (metis assms(5) compat_elim(3) ranI)
      apply (cases "\<rho> k", auto)
       apply (metis compat_elim(3) domIff ranI) 
      apply (auto simp: compat_def env_select_var_compat_def)
      by (smt \<open>(\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) (V y) = Some \<tau>\<close> demote.cases domI dom_def empty_offset_apply fun_upd_apply mem_Collect_eq offset_upd_dif option.simps(5))
  qed
qed

lemma apply_offset_neq[simp]: 
  assumes "j \<noteq> l"
  shows "(\<lambda>k. if l = k then [f] else [])\<^sup>j[\<tau>] = \<tau>"
  using assms
  by (auto simp: apply_offset_def)

lemma env_select_var_compat_apply_f:
  assumes "env_select_var_compat \<Gamma> \<O> \<P> (\<mu>, \<rho>)" 
      and "\<Gamma> (V x) = Some \<tau>"
      and "\<mu> x = Some l" 
      and "type_preserving f"
      and "inj \<mu>"
  shows "env_select_var_compat (\<Gamma>(V x \<mapsto> f \<tau>)) (empty_offset(l @@ f) \<circ>\<^sub>o \<O>) \<P> (\<mu>, \<rho>)"
proof(unfold env_select_var_compat_def, auto)
  obtain \<sigma> where "exactType (\<rho> l) = Some \<sigma>" and "\<O>\<^sup>l[\<P>\<^sup>l[\<sigma>]] \<sqsubseteq>\<^sub>\<tau> \<tau>"
    using assms
    by (metis apply_offset_distrib env_select_var_compat_use)
  then obtain q t where "\<sigma> = (q, t)" by (cases \<sigma>, auto)

  fix k \<tau>'
  assume "\<mu> x = Some k" and "f \<tau> = \<tau>'"
  then have "l = k" using assms(3) domD by auto
  then show "\<exists>aa ba.
              exactType (\<rho> k) = Some (aa, ba) \<and>
              0\<^sub>\<O>(l := 0\<^sub>\<O> l @ [f])\<^sup>k[\<O>\<^sup>k[\<P>\<^sup>k[(aa, ba)]]] \<sqsubseteq>\<^sub>\<tau> \<tau>'"
  proof(intro exI conjI)
    show "exactType (\<rho> k) = Some (q, t)"
      using \<open>\<sigma> = (q, t)\<close> \<open>exactType (\<rho> l) = Some \<sigma>\<close> \<open>l = k\<close> by auto
    show "empty_offset(l := empty_offset l @ [f])\<^sup>k[\<O>\<^sup>k[\<P>\<^sup>k[(q, t)]]] \<sqsubseteq>\<^sub>\<tau> \<tau>'"
      using \<open>f \<tau> = \<tau>'\<close> assms
      apply (auto simp: type_preserving_def)
      by (metis \<open>\<O>\<^sup>l[\<P>\<^sup>l[\<sigma>]] \<sqsubseteq>\<^sub>\<tau> \<tau>\<close> \<open>\<sigma> = (q, t)\<close> \<open>l = k\<close> empty_offset_apply less_general_type.elims(2) offset_upd)
  qed
next
  fix y \<tau> k
  assume "y \<noteq> x" and "\<Gamma> (V y) = Some \<tau>" and "\<mu> y = Some k"
  then obtain \<sigma> where "exactType (\<rho> k) = Some \<sigma>" and "\<O>\<^sup>k[\<P>\<^sup>k[\<sigma>]] \<sqsubseteq>\<^sub>\<tau> \<tau>"
    using assms
    by (metis apply_offset_distrib env_select_var_compat_use)
  then obtain q t where "\<sigma> = (q, t)" by (cases \<sigma>, auto)
  have "l \<noteq> k" using \<open>y \<noteq> x\<close> \<open>inj \<mu>\<close> \<open>\<mu> y = Some k\<close> assms(3) inj_eq by fastforce 
  then show "\<exists>aa ba.
              exactType (\<rho> k) = Some (aa, ba) \<and>
              empty_offset(l := empty_offset l @ [f])\<^sup>k[\<O>\<^sup>k[\<P>\<^sup>k[(aa, ba)]]] \<sqsubseteq>\<^sub>\<tau> \<tau>"
    by (metis \<open>\<O>\<^sup>k[\<P>\<^sup>k[\<sigma>]] \<sqsubseteq>\<^sub>\<tau> \<tau>\<close> \<open>\<sigma> = (q, t)\<close> \<open>exactType (\<rho> k) = Some \<sigma>\<close> empty_offset_apply offset_upd_dif)
qed

lemma locator_preservation:
  fixes "\<Sigma>" and "\<L>" and "\<Sigma>'" and "\<L>'"
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (build_offset f \<L>) \<P> \<Sigma>"
      and "offset_dom \<P> \<subseteq> loc_dom \<Gamma>"
      and "type_preserving_offset \<P>"
      and "type_preserving f"
      and "\<L> wf"
    shows "\<exists>\<Gamma>' \<Delta>'. compat \<Gamma>' (build_offset f \<L>') \<P> \<Sigma>'
                 \<and> (\<Gamma>' \<turnstile>{m} f ; \<L>' : \<tau> \<stileturn> \<Delta>')
                 \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>'
                 \<and> loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'
                 \<and> (\<L>' wf)"
  using assms
proof(induction arbitrary: \<Gamma> \<tau> f m \<Delta> \<P>)
  (* TODO: This is an absurd amount of effort for a relatively easy case... *)
  case (ENat l \<rho> \<mu> n)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> (natural, Num n))" by (auto simp: map_le_def) 
  have "\<tau> = (toQuant n, natural)" using ENat loc_type.cases by blast
  let ?\<L>' = "Loc l"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> (natural, Num n))"
  have compat: "compat ?\<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, ?\<rho>')" using ENat
    using \<open>\<tau> = (toQuant n, natural)\<close> fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (simp_all add: empty_offset_insert)
    using add_fresh_loc less_general_type_refl by auto

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "m = s"
    using ENat.prems
    apply simp
    apply (erule loc_type.cases)
    by auto
  have "\<Delta> = \<Gamma>" using ENat.prems
    apply simp
    apply (erule loc_type.cases)
    by auto

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'" using ENat fresh_loc_not_in_env
    apply (auto simp: map_le_def)
    using ENat.hyps by blast

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, ?\<rho>')"
      and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'"
      and "(\<mu>, \<rho>) \<subseteq>\<^sub>s (\<mu>, ?\<rho>')"
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
      and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using compat typed var_ty_same loc_ty_sub
    by (simp add: \<open>\<rho> \<subseteq>\<^sub>m ?\<rho>'\<close>) 

  then show ?case using ENat.prems \<open>m = s\<close> wf_locator.simps(5) by blast
next
  case (EBool l \<rho> \<mu> b)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> (boolean, Bool b))" by (auto simp: map_le_def) 
  have "\<tau> = (any, boolean)" using EBool loc_type.cases by blast
  let ?\<L>' = "Loc l"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> (boolean, Bool b))"
  have compat: "compat ?\<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, ?\<rho>')" using EBool
    using \<open>\<tau> = (any, boolean)\<close> fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (cases b)
    apply (simp_all add: empty_offset_insert)
    apply (rule add_fresh_loc)
    apply simp_all
    apply (simp_all add: empty_offset_insert)
    apply (rule add_fresh_loc)
    apply simp_all
    by (simp_all add: empty_offset_insert)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "m = s"
    using EBool.prems
    apply simp
    apply (erule loc_type.cases)
    by auto
  have "\<Delta> = \<Gamma>" using EBool.prems using loc_type.cases by blast

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"using EBool fresh_loc_not_in_env
    apply (auto simp: map_le_def)
    using EBool.hyps by blast

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "(\<mu>, \<rho>) \<subseteq>\<^sub>s (\<mu>, ?\<rho>')"
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
      and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using compat typed var_ty_same loc_ty_sub
    by (simp add: \<open>\<rho> \<subseteq>\<^sub>m ?\<rho>'\<close>) 

  then show ?case using EBool.prems \<open>m = s\<close>
    using wf_locator.simps(5) by blast
next
  case (EVar \<mu> x l \<rho>)
  then have x_ty: "\<Gamma> (V x) = Some \<tau>" and final_env: "\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)" 
    apply auto
     apply (erule loc_type.cases)
    apply auto
     apply (erule loc_type.cases)
    by auto

  let ?\<L>' = "Loc l"
  let ?\<Gamma>' = "if ?\<L>' \<in> dom \<Delta> then \<Delta> else \<Delta>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"

  have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" using final_env by simp

  (* TODO: Need to simplify this... *)
  have "\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>" using EVar 
    by (auto simp: compat_def var_store_sync_def)

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'" using final_env
    apply auto
    using map_le_def by fastforce

  then show ?case
  proof(cases "Loc l \<in> dom \<Gamma>")
    case True
      then have a1: "\<Gamma> (V x) = \<Gamma> (Loc l)" using EVar
        using \<open>\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>\<close>
        by (metis (full_types) domD)
      then have a2: "\<Gamma> (Loc l) = Some \<tau>" using x_ty
        by auto
    
      have compat: "compat ?\<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, \<rho>)"
      proof(rule compat_same_store_upd, simp_all add: final_env True)
        show "compat \<Gamma> (build_offset f (S (V x))) \<P> (\<mu>, \<rho>)" using EVar by simp

        show "{xa. xa = x \<or> V xa \<in> dom \<Gamma>} = dom \<mu>" using EVar compat_elim x_ty
          by (metis (mono_tags, lifting) Collect_cong domI var_dom.simps)

        show "var_store_sync (\<Gamma>(V x \<mapsto> f \<tau>)) (\<lambda>k. if l = k then [f] else []) \<mu>"
          using x_ty a1 a2 EVar
          apply (auto simp: var_store_sync_def apply_offset_def)
          using compat_elim injD
          apply metis
          by (simp add: \<open>\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>\<close>)

        have "inj \<mu>" using EVar compat_elim by auto
        then have "\<forall>y. y \<noteq> x \<longrightarrow> \<mu> y \<noteq> Some l"
          using \<open>\<mu> x = Some l\<close> inj_eq by fastforce

        have "\<exists>\<sigma>. exactType (\<rho> l) = Some \<sigma> \<and> (\<P>\<^sup>l[\<sigma>]) \<sqsubseteq>\<^sub>\<tau> \<tau>"
          using EVar.prems(2) a2 compat_elim(8) env_select_loc_compat_use by blast
      
        then show "env_select_var_compat (\<Gamma>(V x \<mapsto> f \<tau>)) (\<lambda>k. if l = k then [f] else []) \<P> (\<mu>, \<rho>)"
          using x_ty a1 a2 EVar
          apply (unfold compat_def)
          apply (auto simp: env_select_var_compat_def type_preserving_def)
          apply (simp add: empty_offset_insert)
           apply (metis empty_offset_apply less_general_type.elims(2) offset_upd)
        proof -
          fix y k \<sigma>'
          assume "\<mu> y = Some k" and "y \<noteq> x" and "\<Gamma> (V y) = Some \<sigma>'"
          then have "k \<noteq> l"
            using \<open>\<forall>y. y \<noteq> x \<longrightarrow> \<mu> y \<noteq> Some l\<close> by auto 
          have "\<forall>x \<tau>' l.
        \<Gamma> (V x) = Some \<tau>' \<and> \<mu> x = Some l \<longrightarrow>
        (\<exists>aa ba. exactType (\<rho> l) = Some (aa, ba) \<and> \<P>\<^sup>l[(aa, ba)] \<sqsubseteq>\<^sub>\<tau> \<tau>')"
            using EVar by (auto simp: compat_def env_select_var_compat_def)
          then have "\<exists>aa ba. exactType (\<rho> k) = Some (aa, ba) \<and> (\<P>\<^sup>k[(aa, ba)]) \<sqsubseteq>\<^sub>\<tau> \<sigma>'"
            using \<open>\<Gamma> (V y) = Some \<sigma>'\<close> \<open>\<mu> y = Some k\<close>
            by blast
          then show "\<exists>a b. exactType (\<rho> k) = Some (a, b) \<and>
                 \<lambda>k. if l = k then [f] else []\<^sup>k[\<P>\<^sup>k[(a, b)]] \<sqsubseteq>\<^sub>\<tau> \<sigma>'"
            by (simp add: \<open>k \<noteq> l\<close>)
        qed

        show "env_select_loc_compat (\<Gamma>(V x \<mapsto> f \<tau>)) \<P> \<rho>"
        proof(auto simp: env_select_loc_compat_def)
          fix k a b
          assume "\<Gamma> (Loc k) = Some (a,b)"
          then show "\<exists>aa ba. exactType (\<rho> k) = Some (aa, ba) \<and> \<P>\<^sup>k[(aa, ba)] \<sqsubseteq>\<^sub>\<tau> (a,b)"
            apply (cases "k = l", auto)
            using \<open>\<exists>\<sigma>. exactType (\<rho> l) = Some \<sigma> \<and> \<P>\<^sup>l[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>\<close> a2 apply auto[1]
            using EVar by (auto simp: compat_def env_select_loc_compat_def)
        qed
      qed
    
      have typed: "?\<Gamma>' \<turnstile>{m} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'"
        by (simp add: Loc final_env a2)
    
      obtain \<Gamma>' and \<Delta>' 
        where "compat \<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, \<rho>)"
          and "\<Gamma>' \<turnstile>{m} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'" 
          and "(\<mu>, \<rho>) \<subseteq>\<^sub>s (\<mu>, \<rho>)"
          and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
          and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
        using compat typed var_ty_same loc_ty_sub by auto

      then show ?thesis using EVar.prems wf_locator.simps(5) by blast 
  next
    case False

    obtain r where in_store: "\<rho> l = Some r" using EVar
      by (meson compat_elim(3) domD in_var_lookup_in_store)

    have compat: "compat ?\<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, \<rho>)" 
      apply (rule compat_same_store_upd[where \<Gamma> = \<Gamma> and \<O> = "build_offset f (S (V x))" and \<P> = \<P>])
      apply (simp_all add: final_env False)
    proof -
      show "compat \<Gamma> empty_offset \<P> (\<mu>, \<rho>)" using EVar by simp

      have "var_dom \<Gamma> = dom \<mu>" using EVar compat_elim by auto
      then show "{xa. xa = x \<or> V xa \<in> dom \<Gamma>} = dom \<mu>"
        using final_env by (auto simp: EVar.hyps)

      show "var_store_sync (\<Gamma>(V x \<mapsto> f \<tau>, Loc l \<mapsto> \<tau>)) (\<lambda>k. if l = k then [f] else []) \<mu>"
        using EVar x_ty
        apply (auto simp: var_store_sync_def)
          apply (simp_all add: apply_offset_def)
        using injD
        apply (metis compat_elim(5))
        by (simp add: \<open>\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>\<close>)

      show "env_select_var_compat (\<Gamma>(V x \<mapsto> f \<tau>, Loc l \<mapsto> \<tau>)) (\<lambda>k. if l = k then [f] else []) \<P> (\<mu>, \<rho>)"
        using EVar x_ty
        apply auto
        apply (rule env_select_var_compat_insert_loc)
        apply (simp add: empty_offset_insert)
        by (metis compat_elim(5) compat_elim(6) env_select_var_compat_apply_f offset_comp_empty_r)

      show "env_select_loc_compat (\<Gamma>(V x \<mapsto> f \<tau>, Loc l \<mapsto> \<tau>)) \<P> \<rho>"
        using EVar x_ty
        by (smt Stored.distinct(1) Stored.inject(2) \<open>Psamathe.compat \<Gamma> 0\<^sub>\<O> \<P> (\<mu>, \<rho>)\<close> compat_elim(6) compat_elim(8) env_select_loc_compat_def env_select_var_compat_use map_upd_Some_unfold offset_comp_empty_l)
    qed

    have typed: "?\<Gamma>' \<turnstile>{m} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'" using False loc_type.Loc 
      apply (simp add: final_env)
      by (metis fun_upd_same fun_upd_upd)

    obtain \<Gamma>' and \<Delta>' 
      where "compat \<Gamma>' (build_offset f (S ?\<L>')) \<P> (\<mu>, \<rho>)"
        and "\<Gamma>' \<turnstile>{m} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'" 
        and "(\<mu>, \<rho>) \<subseteq>\<^sub>s (\<mu>, \<rho>)"
        and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
        and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
      using compat typed var_ty_same loc_ty_sub by auto

    then show ?thesis using EVar.prems wf_locator.simps(5) by blast
  qed
next
  case (EVarDef x \<mu> l \<rho> t)
  then have final_env: "\<Delta> = \<Gamma>(V x \<mapsto> f (empty,t))" by simp (erule loc_type.cases, auto)

  let ?\<L>' = "Loc l"
  let ?\<Gamma>' = "\<Delta>(?\<L>' \<mapsto> (empty,t))"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f (empty,t))"
  let ?\<mu>' = "\<mu>(x \<mapsto> l)"
  let ?\<rho>' = "\<rho>(l \<mapsto> (t, emptyVal t))"

  have compat: "compat ?\<Gamma>' (build_offset f (S ?\<L>')) \<P> (?\<mu>', ?\<rho>')" 
  proof(rule compatI)
    show "var_dom (\<Delta>(Loc l \<mapsto> (empty, t))) = dom (\<mu>(x \<mapsto> l))"
      using final_env EVarDef by (auto simp: compat_def)

    show "\<forall>k. k \<notin> dom (\<rho>(l \<mapsto> (t, emptyVal t))) \<longrightarrow> k \<notin> ran (\<mu>(x \<mapsto> l))"
      using EVarDef by (auto simp: compat_def)

    show "var_store_sync (\<Delta>(Loc l \<mapsto> (empty, t))) (build_offset f (S (Loc l))) (\<mu>(x \<mapsto> l))"
      using EVarDef final_env
      apply (unfold compat_def var_store_sync_def)
      apply (auto simp: apply_offset_def)
       apply (metis EVarDef.hyps(2) ranI)
      by (auto simp: empty_offset_def)

    show "inj (\<mu>(x \<mapsto> l))"
      using EVarDef compat_elim
      apply auto
      by (smt EVarDef.hyps(2) fun_upd_apply inj_on_def ranI)

    show "env_select_var_compat ?\<Gamma>' (build_offset f (S (Loc l))) \<P> (?\<mu>', ?\<rho>')"
      using EVarDef
      apply (simp add: final_env empty_offset_insert)
      apply (rule env_select_var_compat_insert_loc)
      apply (rule env_select_var_compat_insert_var)
      apply auto
      apply (meson EVarDef.hyps(1) compat_elim(1) compat_elim(6) domI in_type_env_compat)
      by (metis EVarDef.hyps(2) in_mono mem_Collect_eq not_in_dom_compat)

    show "finite (dom ?\<rho>')"
      using EVarDef by (auto simp: compat_def)

    have "env_select_loc_compat \<Gamma> \<P> \<rho>" using EVarDef compat_elim by auto
    have "l \<notin> offset_dom \<P>"
      using EVarDef
      by (metis loc_dom.simps mem_Collect_eq not_in_dom_compat subsetD)
    then show "env_select_loc_compat ?\<Gamma>' \<P> ?\<rho>'"
      apply (simp add: final_env)
      apply (auto simp: env_select_loc_compat_def not_in_offset_dom_is_id)
      using \<open>env_select_loc_compat \<Gamma> \<P> \<rho>\<close>
      by (auto simp: env_select_loc_compat_def)

    show "\<forall>la ta v. (\<rho>(l \<mapsto> (t, emptyVal t))) la = Some (ta, v) \<longrightarrow> baseTypeMatches ta v"
      using EVarDef compat_elim
      by (simp add: baseTypeMatches_emptyVal_works)
  qed

  have typed: "?\<Gamma>' \<turnstile>{m} f ; S ?\<L>' : (empty,t) \<stileturn> ?\<Delta>'"
    by (meson Loc fun_upd_same)

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    apply (auto simp: map_le_def final_env)
    apply (metis EVarDef.hyps(2) EVarDef.prems(2) domI not_in_dom_compat)
    by (metis EVarDef.hyps(2) EVarDef.prems(2) domI not_in_dom_compat)

  have "\<tau> = (empty,t)" using EVarDef loc_type.cases by blast

  then show ?case
    using \<open>\<tau> = (TyQuant.empty, t)\<close> compat loc_ty_sub typed var_ty_same
    by (smt EVarDef.hyps(1) EVarDef.hyps(2) fun_upd_other map_le_def sub_store.simps wf_locator.simps(5))
next               
  case (EConsListHeadCongr \<Sigma> \<L> \<Sigma>' \<L>' \<tau>' Tail \<Gamma> \<tau>)

  have "\<L> wf" using EConsListHeadCongr by auto

  obtain \<Delta>'' and q
    where "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''" and tail_ty: "\<Delta>'' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Delta>"
      and "\<tau> = (one \<oplus> q, table [] \<tau>')" and "m = s"
    using EConsListHeadCongr 
    apply auto
    using step_not_located apply auto[1] 
     apply (erule loc_type.cases)
    by blast+

  have "locations Tail = {#}" and "Tail wf" using EConsListHeadCongr
    using head_step_wf(1) apply blast
    using EConsListHeadCongr head_step_wf by blast

  then obtain \<Gamma>' and \<Delta>' 
    where "compat \<Gamma>' (build_offset f \<L>') \<P> \<Sigma>'" 
      and "\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'" 
      and var_env_eq: "var_ty_env \<Delta>'' = var_ty_env \<Delta>'"
      and loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using EConsListHeadCongr \<open>\<L> wf\<close>
    apply simp
    by (metis \<open>\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''\<close> build_offset_no_locs offset_comp_empty_l)

  then obtain \<Xi>' 
    where "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Xi>'" 
      and "var_ty_env \<Delta> = var_ty_env \<Xi>'"
      and "loc_ty_env \<Xi>' = loc_ty_env \<Delta>'"
      and "\<Sigma> \<subseteq>\<^sub>s \<Sigma>'"
    using EConsListHeadCongr tail_ty prf_compat_not_located var_env_eq
    by (smt \<open>Tail wf\<close> \<open>\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''\<close> \<open>\<L> wf\<close> \<open>locations Tail = {#}\<close> build_offset.simps(7) build_offset_no_locs offset_comp_empty_l)

  then show ?case
  proof(intro exI conjI)
    show "compat \<Gamma>' (build_offset f [ \<tau>' ; \<L>' , Tail ]) \<P> \<Sigma>'"
      using \<open>Psamathe.compat \<Gamma>' (build_offset f \<L>') \<P> \<Sigma>'\<close> \<open>locations Tail = {#}\<close>
      by (simp add: build_offset_no_locs)
    show "var_ty_env \<Delta> = var_ty_env \<Xi>'"
      using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>'\<close> by auto
    show "\<Gamma>' \<turnstile>{m} f ; [ \<tau>' ; \<L>' , Tail ] : \<tau> \<stileturn> \<Xi>'" using \<open>\<tau> = (one \<oplus> q, table [] \<tau>')\<close> \<open>m = s\<close>
      apply simp
    proof(rule loc_type.ConsList)
      show "\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'"
        by (simp add: \<open>\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'\<close>)
      show "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Xi>'"
        by (simp add: \<open>\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Xi>'\<close>)
    qed
    show "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'" using loc_ty_sub by simp
    show "\<Sigma> \<subseteq>\<^sub>s \<Sigma>'" by (simp add: \<open>\<Sigma> \<subseteq>\<^sub>s \<Sigma>'\<close>) 
    show "[ \<tau>' ; \<L>' , Tail ] wf"
      by (metis EConsListHeadCongr.IH EConsListHeadCongr.prems(2) EConsListHeadCongr.prems(3) EConsListHeadCongr.prems(4) EConsListHeadCongr.prems(5) \<open>Tail wf\<close> \<open>\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''\<close> \<open>\<L> wf\<close> \<open>locations Tail = {#}\<close> build_offset.simps(7) build_offset_no_locs offset_comp_empty_l wf_locator.simps(2))
  qed
next
  case (EConsListTailCongr \<L> \<Sigma> Tail \<Sigma>' Tail' \<tau>')

  obtain \<Delta>'' and q
    where head_ty: "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''" 
      and tail_ty: "\<Delta>'' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Delta>"
      and "\<tau> = (one \<oplus> q, table [] \<tau>')"
      and "m = s"
    using EConsListTailCongr 
    apply auto 
    apply (erule loc_type.cases)
    by blast+

  obtain \<mu> \<rho> where "\<Sigma> = (\<mu>, \<rho>)" by (cases \<Sigma>)

  have "\<L> wf" and "Tail wf" using EConsListTailCongr by auto
  have "compat \<Delta>'' (build_offset f Tail) (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>,\<rho>)" 
    apply (rule located_env_compat2)
    using EConsListTailCongr \<open> located \<L> \<close> head_ty \<open>\<L> wf\<close> \<open>Tail wf\<close>
    apply auto
    using \<open>\<Sigma> = (\<mu>, \<rho>)\<close>
    by blast

  from \<open>\<L> wf\<close> and \<open>Tail wf\<close> have a2: "update_locations \<Gamma> (build_offset f \<L>) = \<Delta>''"
    using EConsListTailCongr \<open>\<Sigma> = (\<mu>, \<rho>)\<close> head_ty located_env_compat 
    by auto      

  have "\<exists>\<Gamma>' \<Delta>'.
           compat \<Gamma>' (build_offset f Tail') (build_offset f \<L> \<circ>\<^sub>o \<P>) \<Sigma>' \<and>
           (\<Gamma>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Delta>') \<and> 
           var_ty_env \<Delta> = var_ty_env \<Delta>' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>' \<and>
           loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Gamma>'
           \<and> (Tail' wf)"
  proof(rule EConsListTailCongr.IH)
    show "\<Delta>'' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Delta>" using tail_ty by simp
    show "compat \<Delta>'' (build_offset f Tail) (build_offset f \<L> \<circ>\<^sub>o \<P>) \<Sigma>"
      by (simp add: \<open>Psamathe.compat \<Delta>'' (build_offset f Tail) (build_offset f \<L> \<circ>\<^sub>o \<P>) (\<mu>, \<rho>)\<close> \<open>\<Sigma> = (\<mu>, \<rho>)\<close>)
    show "type_preserving f" using EConsListTailCongr by simp
    show "Tail wf" using \<open>Tail wf\<close> by simp
    show "offset_dom (build_offset f \<L> \<circ>\<^sub>o \<P>) \<subseteq> loc_dom \<Delta>''"
      by (smt EConsListTailCongr.hyps(1) EConsListTailCongr.prems(3) a2 env_dom_eq_sub_dom_eq head_ty in_mono located_locations_in_offset_dom offset_dom_member_distrib subsetI update_loc_preserve_dom) 
    show "type_preserving_offset (build_offset f \<L> \<circ>\<^sub>o \<P>)"
      by (simp add: EConsListTailCongr.prems(4) EConsListTailCongr.prems(5) type_preserving_build type_preserving_offset_comp)
  qed

  then obtain \<Delta>' \<Xi> 
    where temp_compat: "compat \<Delta>' (build_offset f Tail') (build_offset f \<L> \<circ>\<^sub>o \<P>) \<Sigma>'"
      and "\<Delta>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Xi>" 
      and "var_ty_env \<Delta> = var_ty_env \<Xi>"
      and "\<Sigma> \<subseteq>\<^sub>s \<Sigma>'"
      and "loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
    using EConsListTailCongr tail_ty \<open> Tail wf \<close> \<open>\<Sigma> = (\<mu>, \<rho>)\<close>
    by blast

  let ?\<Gamma>' = "temp_update_env \<Gamma> \<Delta>'"
  have "?\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>'"
    using EConsListTailCongr.hyps(1) \<open>loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'\<close> head_ty located_var_ignore by auto

  have "offset_dom (build_offset f \<L>) \<subseteq> loc_dom \<Gamma>"
    using EConsListTailCongr.hyps(1) head_ty located_locations_in_offset_dom by auto

  then have "update_locations ?\<Gamma>' (build_offset f \<L>) = \<Delta>'" using a2
    using \<open>loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'\<close> temp1 by auto

  then show ?case
  proof(intro exI conjI)
    (* TODO: Cleanup *)

    obtain \<mu>' \<rho>' where "\<Sigma>' = (\<mu>', \<rho>')" by (cases \<Sigma>')
    have "env_select_loc_compat \<Gamma> \<P> \<rho>" using EConsListTailCongr.prems(2) \<open>\<Sigma> = (\<mu>, \<rho>)\<close> by auto
    then show "compat ?\<Gamma>' (build_offset f [ \<tau>' ; \<L> , Tail' ]) \<P> \<Sigma>'" using \<open>\<Sigma>' = (\<mu>', \<rho>')\<close>
      apply auto    
      apply (rule temp2)
      using \<open>update_locations (temp_update_env \<Gamma> \<Delta>') (build_offset f \<L>) = \<Delta>'\<close> temp_compat apply auto[1]
      apply (simp add: EConsListTailCongr.prems(5) type_preserving_build)
      apply (simp add: EConsListTailCongr.prems(4))
      using \<open>offset_dom (build_offset f \<L>) \<subseteq> loc_dom \<Gamma>\<close> apply auto[1]
      apply (rule refl)
        apply (simp add: \<open>update_locations (temp_update_env \<Gamma> \<Delta>') (build_offset f \<L>) = \<Delta>'\<close>)
      apply assumption
      using \<open>\<Sigma> = (\<mu>, \<rho>)\<close> \<open>\<Sigma> \<subseteq>\<^sub>s \<Sigma>'\<close> by auto

    show "var_ty_env \<Delta> = var_ty_env \<Xi>" using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>\<close> by simp

    show "?\<Gamma>' \<turnstile>{m} f ; [ \<tau>' ; \<L> , Tail' ] : \<tau> \<stileturn> \<Xi>"
      using ConsList \<open>\<Delta>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Xi>\<close> \<open>\<tau> = (one \<oplus> q, table [] \<tau>')\<close> \<open>m = s\<close> \<open>temp_update_env \<Gamma> \<Delta>' \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>'\<close> by auto

    show "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'" by (auto simp: map_le_def)
    show "\<Sigma> \<subseteq>\<^sub>s \<Sigma>'" by (simp add: \<open>\<Sigma> \<subseteq>\<^sub>s \<Sigma>'\<close>) 

    show "[ \<tau>' ; \<L> , Tail' ] wf"
      using EConsListTailCongr.hyps(1) \<open>\<L> wf\<close> \<open>\<exists>\<Gamma>' \<Delta>'''. Psamathe.compat \<Gamma>' (build_offset f Tail') (build_offset f \<L> \<circ>\<^sub>o \<P>) \<Sigma>' \<and> \<Gamma>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Delta>''' \<and> var_ty_env \<Delta> = var_ty_env \<Delta>''' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>' \<and> loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Gamma>' \<and> (Tail' wf)\<close> by auto
  qed
next
  case (ECopyCongr \<Sigma> L \<Sigma>' L')

  then obtain \<sigma> 
    where loc_ty: "\<Gamma> \<turnstile>{s} id ; L : \<sigma> \<stileturn> \<Gamma>" and "demote \<sigma> = \<tau>" and final_env: "\<Gamma> = \<Delta>" and "m = s"
    apply auto
    apply (erule loc_type.cases)
    by auto

  have "\<exists>\<Gamma>' \<Delta>'. compat \<Gamma>' (build_offset id L') \<P> \<Sigma>' \<and>
           (\<Gamma>' \<turnstile>{s} id ; L' : \<sigma> \<stileturn> \<Delta>') \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' \<and> 
           \<Sigma> \<subseteq>\<^sub>s \<Sigma>' \<and> loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>' \<and> (L' wf)"
  proof(rule ECopyCongr.IH)
    show "\<Gamma> \<turnstile>{s} id ; L : \<sigma> \<stileturn> \<Delta>" using loc_ty final_env by simp

    show "compat \<Gamma> (build_offset id L) \<P> \<Sigma>" using ECopyCongr
      apply simp
      by (metis compat_elim(4) compat_elim(6) compat_transfer_var_sync env_select_var_compat_id finite_store.cases offset_comp_empty_l var_store_sync_build_id)

    show "type_preserving id" by (simp add: type_preserving_id)
    show "L wf" using ECopyCongr by simp 
    show "offset_dom \<P> \<subseteq> loc_dom \<Gamma>" using ECopyCongr by auto
    show "type_preserving_offset \<P>" using ECopyCongr by auto
  qed

  then have "\<exists>\<Gamma>' \<Delta>'. compat \<Gamma>' (build_offset id L') \<P> \<Sigma>' \<and>
           (\<Gamma>' \<turnstile>{s} f ; copy(L') : demote \<sigma> \<stileturn> \<Delta>') 
           \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>' \<and> loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using Copy typecheck_id_env_same_source by blast

  then show ?case using \<open>demote \<sigma> = \<tau>\<close>
    apply auto
    by (metis \<open>\<exists>\<Gamma>'' \<Delta>''. Psamathe.compat \<Gamma>'' (build_offset id L') \<P> \<Sigma>' \<and> \<Gamma>'' \<turnstile>{s} id ; L' : \<sigma> \<stileturn> \<Delta>'' \<and> var_ty_env \<Delta> = var_ty_env \<Delta>'' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>' \<and> loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'' \<and> (L' wf)\<close> \<open>m = s\<close> compat_id surj_pair)
qed

fun build_stmt_offset :: "Env \<Rightarrow> Stmt \<Rightarrow> nat Offset" where
  "build_stmt_offset \<Gamma> (Src \<longlonglongrightarrow> Dst) = 
    (case typecheck \<Gamma> s (\<lambda>(_,t). (empty, t)) Src of
      Some ((q,_), \<Delta>) \<Rightarrow> build_offset (\<lambda>(r,s). (r \<oplus> q, s)) Dst \<circ>\<^sub>o build_offset (\<lambda>(_,t). (empty,t)) Src
    | _ \<Rightarrow> 0\<^sub>\<O>)"
| "build_stmt_offset \<Gamma> Revert = 0\<^sub>\<O>"

lemma type_preserving_add: "type_preserving (\<lambda>(r, s). (r \<oplus> q, s))"
  apply (auto simp: type_preserving_def)
  using quant_add_comm quant_add_lt_left by auto

lemma loc_typed_src:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "m = s"
      and "\<And>n. L = N n \<Longrightarrow> P L"
      and "\<And>b. L = B b \<Longrightarrow> P L"
      and "\<And>x. L = S x \<Longrightarrow> P L"
      and "\<And>q k \<sigma>. \<lbrakk> \<tau> = (q, table k \<sigma>); L = [ \<sigma>; ] \<rbrakk> \<Longrightarrow> P L"
      and "\<And>q k \<sigma> Head Tail. \<lbrakk> \<tau> = (q, table k \<sigma>); L = [ \<sigma> ; Head, Tail ] \<rbrakk> \<Longrightarrow> P L"
      and "\<And>L'. \<lbrakk> L = copy(L') \<rbrakk> \<Longrightarrow> P L"
    shows "P L"
  using assms
  by (induction, auto)

lemma loc_typed_dst:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "m = d"
      and "\<And>x t. L = var x : t \<Longrightarrow> P L"
      and "\<And>x. L = S x \<Longrightarrow> P L"
    shows "P L"
  using assms
  by (induction, auto)

lemma stmt_wf_src_wf:
  assumes "Src \<longlonglongrightarrow> Dst stmt_wf"
  shows "Src wf"
  using assms
  by (cases Src, auto)

lemma stmt_progress:
  (* TODO: This isn't ideal, but I need to get the quantity in somehow... *)
  assumes "\<Gamma> \<turnstile> Stmt ok \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_stmt_offset \<Gamma> Stmt) empty_offset (\<mu>, \<rho>)"
      and "Stmt stmt_wf"
      and "finite (dom \<rho>)"
    shows "Stmt = Revert \<or> (\<exists>\<mu>' \<rho>' Stmts'. \<langle> (\<mu>, \<rho>), [Stmt] \<rangle> \<rightarrow> \<langle> (\<mu>', \<rho>'), Stmts' \<rangle>)"
  (* TODO: Maybe need to split this into more lemmas, because I don't really like the 
            super deep case nesting... *)
  using assms
proof(induction arbitrary: \<O> \<mu> \<rho>)
  case (Flow \<Gamma> Src q t \<Delta> Dst r \<Xi>)
  then have typecheck_match: "typecheck \<Gamma> s (\<lambda>(_, t). (empty, t)) Src = Some ((q,t), \<Delta>)"
    by (simp add: typecheck_matches_loc_type)
  then show ?case
  proof(cases "located Src")
    case True
    then show ?thesis
    proof(cases "located Dst")
      case True
      show ?thesis
      proof(rule loc_typed_src[where L = Src])
        show "\<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; Src : (q,t) \<stileturn> \<Delta>" using Flow by simp
        show "s = s" by simp
      next
        fix n
        assume "Src = N n"
        then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
          using \<open>located Src\<close> True by auto
      next
        fix b
        assume "Src = B b"
        then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
          using \<open>located Src\<close> True by auto
      next
        fix x
        assume src: "Src = S x"
        then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
        proof(cases x)
          case (V x1)
          then show ?thesis using \<open>located Src\<close> src by simp
        next
          case (Loc x2)
          have "\<Gamma> x = Some (q,t)"
            using Flow.hyps(1) src
            apply auto
            apply (erule loc_type.cases)
            by auto
          then obtain parent_res where parent: "\<rho> x2 = parent_res"
            using Flow src True typecheck_match
            by auto
          show ?thesis
          proof(rule loc_typed_dst)
            show "\<Delta> \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r,t) \<stileturn> \<Xi>" using Flow by simp
            show "d = d" by simp
          next
            fix x t 
            assume "Dst = var x : t" 
            then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
              using True by auto
          next
            fix y
            assume dst: "Dst = S y" 
            then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
            proof(cases y)
              case (V x1)
              then show ?thesis using True \<open>Dst = S y\<close> by auto
            next
              case (Loc y2)
              then have "\<Delta> y = Some (r,t)"
                using Flow.hyps(2) dst
                apply auto
                apply (erule loc_type.cases)
                by auto
              have "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset (\<lambda>(r, y). (r \<oplus> q, y)) Dst) 
                                   (build_offset (\<lambda>(_, y). (empty, y)) Src \<circ>\<^sub>o 0\<^sub>\<O>)
                                   (\<mu>, \<rho>)"
                apply (rule located_env_compat2(1))
                using Flow.hyps(1) apply assumption
                using Flow typecheck_match \<open>located Src\<close> apply auto
                apply (simp add: offset_comp_assoc)
                by (simp add: type_preserving_with_quant)
              then obtain dest_res where dest_eq: "(\<rho>(x2 := parent_res -\<^sub>r parent_res)) y2 = dest_res"
                using Flow dst
                by simp
              then show ?thesis using src Loc dst \<open>x = Loc x2\<close>
                apply (cases "parent_res -\<^sub>r parent_res \<noteq> None \<and> dest_res +\<^sub>r parent_res \<noteq> None")
                apply (intro exI disjI2)
                apply simp
                apply (rule EFlowLoc)
                using parent apply auto
                apply (metis EFlowLocFail old.prod.exhaust option.exhaust)
                apply (intro exI disjI2)
                apply (rule EFlowLocFail)
                by auto
            qed
          qed
        qed
      next
        fix q' k \<sigma>
        assume "(q, t) = (q', table k \<sigma>)" and "Src = [ \<sigma> ; ]"
        then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
          using EFlowEmptyList True by blast
      next
        fix q' k \<sigma> Head Tail
        assume "(q, t) = (q', table k \<sigma>)" and "Src = [ \<sigma> ; Head , Tail ]"
        then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
          apply (intro exI disjI2)
          apply simp
          apply (rule EFlowConsList)
          using \<open>located Src\<close> apply simp
          using \<open>located Src\<close> apply simp
          using \<open>located Dst\<close> by simp
      next
        fix L'
        obtain l where fresh: "l \<notin> dom \<rho>" using Flow gen_loc by auto
        assume "Src = copy(L')" 
        then show "(Src \<longlonglongrightarrow> Dst) = Revert \<or> (\<exists>\<mu>'' \<rho>'' a. \<langle> (\<mu>, \<rho>) , [Src \<longlonglongrightarrow> Dst] \<rangle> \<rightarrow> \<langle> (\<mu>'', \<rho>'') , a \<rangle>)"
          apply simp
          apply (intro exI disjI2)
          apply (rule EFlowCopy)
          using \<open>located Src\<close> apply simp
          using Flow.prems(2) apply auto[1]
          using fresh by simp
      qed
    next
      case False
      have "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset (\<lambda>(r, s). (r \<oplus> q, s)) Dst) 
                      ((build_offset (\<lambda>(_,t). (empty,t)) Src) \<circ>\<^sub>o 0\<^sub>\<O>) (\<mu>, \<rho>) 
          \<and> \<Delta> = update_locations \<Gamma> (build_offset (\<lambda>(_,t). (empty,t)) Src)"
      proof(rule located_env_compat)
        show "\<Gamma> \<turnstile>{s} \<lambda>(_, t). (empty, t) ; Src : (q, t) \<stileturn> \<Delta>" using Flow by simp
        
        show "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset (\<lambda>(r, s). (r \<oplus> q, s)) Dst \<circ>\<^sub>o build_offset (\<lambda>(_, t). (empty, t)) Src)
                     0\<^sub>\<O> (\<mu>, \<rho>)"
          using Flow typecheck_match by (auto simp: offset_comp_assoc)
  
        show "located Src" using \<open>located Src\<close> by simp
        show "type_preserving (\<lambda>(_, t). (empty, t))" using type_preserving_with_quant by simp
      qed
      
      then have dst_compat: "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset (\<lambda>(r, s). (r \<oplus> q, s)) Dst) 
                                        (build_offset (\<lambda>(_,t). (empty,t)) Src) (\<mu>, \<rho>)"
        by (metis offset_comp_empty_r)
      have "located Dst \<or> (\<exists>\<mu>' \<rho>' Dst'. <(\<mu>, \<rho>), Dst> \<rightarrow> <(\<mu>', \<rho>'), Dst'>)"
      proof(rule locator_progress)
        show "\<Delta> \<turnstile>{d} \<lambda>(r, s). (r \<oplus> q, s) ; Dst : (r, t) \<stileturn> \<Xi>" using Flow by simp
  
        show "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset (\<lambda>(r, s). (r \<oplus> q, s)) Dst) (build_offset (\<lambda>(_,t). (empty,t)) Src) (\<mu>, \<rho>)"
          using dst_compat by simp
  
        show "Dst wf" using Flow
          using loc_typed_dst wf_locator.simps(5) wf_locator.simps(6) by blast
        show "finite (dom \<rho>)" using Flow by simp
        show "type_preserving (\<lambda>(r, s). (r \<oplus> q, s))" using type_preserving_add by simp
      qed
      then obtain \<mu>' \<rho>' Dst' where step: "<(\<mu>, \<rho>), Dst> \<rightarrow> <(\<mu>', \<rho>'), Dst'>" using False by auto

      obtain l where fresh: "l \<notin> dom \<rho>" using Flow gen_loc by auto
        
      show ?thesis
      proof(cases "\<exists>L. Src = copy(L)")
        case True
        then obtain L where "Src = copy(L)" by auto        

        then show ?thesis 
          apply (intro exI disjI2, simp)
          apply (rule EFlowCopy)
          using \<open>located Src\<close> apply simp
          using Flow apply simp
          using fresh by assumption
      next
        case False
        then show ?thesis
          using \<open>located Src\<close> locator_progress type_preserving_add step
          apply (intro exI disjI2)
          apply (rule EFlowDstCongr[where \<Sigma>' = "(\<mu>', \<rho>')" and Dst' = Dst'])
          apply simp
          by simp 
      qed
    qed
  next
    case False
    have "located Src \<or> (\<exists>\<mu>' \<rho>' Src'. < (\<mu>, \<rho>) , Src > \<rightarrow> < (\<mu>', \<rho>') , Src' >)"
      apply (rule locator_progress)
      using Flow.hyps(1) apply assumption
      using Flow typecheck_match apply auto
      using False apply (cases "\<exists>L. Src = copy(L)", auto)
      apply (simp add: offset_comp_assoc)
      by (simp add: type_preserving_with_quant)
    then show ?thesis using Flow EFlowSrcCongr False by blast
  qed
next
  case (Revert \<Gamma>)
  then show ?case by simp
qed

fun build_stmts_offset :: "Env \<Rightarrow> Stmt list \<Rightarrow> nat Offset" where
  "build_stmts_offset \<Gamma> [] = empty_offset"
| "build_stmts_offset \<Gamma> (S1 # \<S>) = (build_stmts_offset (typecheck_stmt \<Gamma> S1) \<S> \<circ>\<^sub>o build_stmt_offset \<Gamma> S1)"
  
theorem stmts_progress:
  assumes "\<Gamma> \<turnstile> Stmts oks \<stileturn> \<Delta>"
      and "compat \<Gamma> (build_stmts_offset \<Gamma> Stmts) empty_offset (\<mu>, \<rho>)"
      and "Stmts stmts_wf"
      and "finite (dom \<rho>)"
    shows "Stmts = [] \<or> (\<exists>\<S>. Stmts = Revert # \<S>)  \<or> (\<exists>\<mu>' \<rho>' Stmts'. \<langle> (\<mu>, \<rho>), Stmts \<rangle> \<rightarrow> \<langle> (\<mu>', \<rho>'), Stmts' \<rangle>)"
  using assms
proof(induction Stmts arbitrary: \<Gamma> \<Delta> \<mu> \<rho>)
case Nil
  then show ?case by auto
next
  case (Cons S1 Stmts)
  then have "S1 stmt_wf" and "Stmts stmts_wf" 
    using wf_stmt.cases
    apply auto
    by (cases Stmts, auto)
  obtain \<Delta>' where "\<Gamma> \<turnstile> S1 ok \<stileturn> \<Delta>'" and "\<Delta>' \<turnstile> Stmts oks \<stileturn> \<Delta>"
    using Cons by auto
  then show ?case
  proof(cases S1)
    case (Flow Src Dst)
    then obtain \<mu>' \<rho>' \<S>\<^sub>1' where "\<langle>(\<mu>, \<rho>), [S1]\<rangle> \<rightarrow> \<langle>(\<mu>', \<rho>'), \<S>\<^sub>1'\<rangle>"
      by (smt Cons.prems(2) Cons.prems(4) Stmt.distinct(1) \<open>S1 stmt_wf\<close> \<open>\<Gamma> \<turnstile> S1 ok \<stileturn> \<Delta>'\<close> build_stmts_offset.simps(2) stmt_progress)
    then show ?thesis
      apply (intro disjI2 exI)
      apply (rule EStmtsCongr)
      by assumption
  next
    case Revert
    then show ?thesis by simp
  qed
qed

lemma located_var_env_same:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "located L"
    shows "var_ty_env \<Gamma> = var_ty_env \<Delta>"
  using assms
  by (induction, auto)

lemma update_locations_var_ty_env_id: 
  "var_ty_env \<Gamma> = var_ty_env (update_locations \<Gamma> \<O>)"
  by simp

lemma offset_uncomp_prop:
  assumes "\<And>\<O> \<P>. P (\<O> \<circ>\<^sub>o \<P>)"
  shows "P \<P>" and "P \<O>"
  using assms
  apply (metis offset_comp_empty_r)
  by (metis assms offset_comp_empty_r)

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

lemma located_dom_same:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    and "located L"
  shows "dom \<Gamma> = dom \<Delta>"
  using assms
  by (induction, auto)

lemma located_add_env:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    and "located L"
    and "dom \<Gamma> \<inter> dom \<Gamma>' = {}"
  shows "(\<Gamma> ++ \<Gamma>') \<turnstile>{m} f ; L : \<tau> \<stileturn> (\<Delta> ++ \<Gamma>')"
  using assms
  apply (induction)
  apply auto
  apply (metis (no_types, hide_lams) Loc disjoint_iff_not_equal domI map_add_comm map_add_find_right map_add_upd_left)
  apply (simp add: EmptyList)
  apply (simp add: ConsList located_dom_same)
  using Copy by auto[1]

lemma located_env_insert:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    and "located L"
    and "x \<notin> dom \<Gamma>"
  shows "(\<Gamma>(x \<mapsto> \<sigma>)) \<turnstile>{m} f ; L : \<tau> \<stileturn> (\<Delta>(x \<mapsto> \<sigma>))"
proof -
  have "(\<Gamma> ++ [x \<mapsto> \<sigma>]) \<turnstile>{m} f ; L : \<tau> \<stileturn> (\<Delta> ++ [x \<mapsto> \<sigma>])"
    apply (rule located_add_env)
    using assms by auto
  then show ?thesis by auto
qed

lemma no_locations_build_stmt_offset_is_empty:
  assumes "stmt_locations Stmt = {#}"
  shows "build_stmt_offset \<Gamma> Stmt = 0\<^sub>\<O>"
  using assms
proof(cases Stmt)
  case (Flow Src Dst)
  then show ?thesis 
    using assms
    apply auto
    apply (cases "typecheck \<Gamma> s (\<lambda>(_, y). (TyQuant.empty, y)) Src")
    apply auto
    by (simp add: no_locations_build_offset_empty)
next
  case Revert
  then show ?thesis by simp
qed

lemma no_locations_build_stmts_offset_is_empty:
  assumes "\<forall>Stmt \<in> set Stmts. stmt_locations Stmt = {#}"
  shows "build_stmts_offset \<Gamma> Stmts = 0\<^sub>\<O>"
  using assms
  apply (induction Stmts arbitrary: \<Gamma>)
  apply auto
  by (simp add: no_locations_build_stmt_offset_is_empty)

lemma stmts_wf_suf_wf:
  assumes "(\<S>\<^sub>1 @ \<S>\<^sub>2) stmts_wf"
  shows "\<S>\<^sub>2 stmts_wf"
  using assms
  apply (induction \<S>\<^sub>2)
   apply auto
  by (cases \<S>\<^sub>1, auto)+

lemma build_stmts_append[simp]:
  "build_stmts_offset \<Gamma> (\<S>\<^sub>1 @ \<S>\<^sub>2) = build_stmts_offset (foldl typecheck_stmt \<Gamma> \<S>\<^sub>1) \<S>\<^sub>2 \<circ>\<^sub>o build_stmts_offset \<Gamma> \<S>\<^sub>1"
  apply (induction \<S>\<^sub>1 arbitrary: \<Gamma> \<S>\<^sub>2, auto)
  by (simp add: offset_comp_assoc)

lemma stmt_append_ok:
  assumes "\<Gamma> \<turnstile> \<S>\<^sub>1 oks \<stileturn> \<Delta>" and "\<Delta> \<turnstile> \<S>\<^sub>2 oks \<stileturn> \<Xi>"
  shows "\<Gamma> \<turnstile> (\<S>\<^sub>1 @ \<S>\<^sub>2) oks \<stileturn> \<Xi>"
  using assms
  by (induction \<S>\<^sub>1 arbitrary: \<Gamma> \<Delta> \<S>\<^sub>2 \<Xi>, auto)

lemma prf_compat_not_located_stmt:
  assumes "\<Gamma> \<turnstile> Stmt ok \<stileturn> \<Delta>"
      and "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
      and "Stmt stmt_wf"
      and "stmt_locations Stmt = {#}"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile> Stmt ok \<stileturn> \<Delta>') 
              \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' 
              \<and> loc_ty_env \<Delta>' = loc_ty_env \<Gamma>'"
  using assms
proof(induction arbitrary: \<Gamma>')
  case (Flow \<Gamma> Src q t \<Delta> Dst uu \<Xi>)

  have "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{s} \<lambda>(_, t). (empty, t) ; Src : (q, t) \<stileturn> \<Delta>') 
                \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' \<and> loc_ty_env \<Delta>' = loc_ty_env \<Gamma>'"
    apply (rule prf_compat_not_located)
    using Flow(1) apply assumption
    using Flow.prems(1) apply auto[1]
    using Flow.prems(2) stmt_wf_src_wf apply blast
    using Flow by auto

  then obtain \<Delta>' 
    where src_ty_new: "\<Gamma>' \<turnstile>{s} \<lambda>(_, t). (empty, t) ; Src : (q, t) \<stileturn> \<Delta>'" 
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'" 
      and loc_ty_new: "loc_ty_env \<Delta>' = loc_ty_env \<Gamma>'"
    by auto

  have "\<exists>\<Xi>'. (\<Delta>' \<turnstile>{d} \<lambda>(r, s). (r \<oplus> q, s) ; Dst : (uu, t) \<stileturn> \<Xi>') 
                \<and> var_ty_env \<Xi> = var_ty_env \<Xi>' \<and> loc_ty_env \<Xi>' = loc_ty_env \<Delta>'"
    apply (rule prf_compat_not_located)
    using Flow(2) apply assumption
    using \<open>var_ty_env \<Delta> = var_ty_env \<Delta>'\<close> apply auto[1]
    using Flow by auto

  then obtain \<Xi>'
    where "\<Delta>' \<turnstile>{d} \<lambda>(r, s). (r \<oplus> q, s) ; Dst : (uu, t) \<stileturn> \<Xi>'"
      and "var_ty_env \<Xi> = var_ty_env \<Xi>'"
      and "loc_ty_env \<Xi>' = loc_ty_env \<Delta>'"
    by auto

  then show ?case using src_ty_new loc_ty_new stmt_ok.Flow by fastforce
next
  case (Revert \<Gamma>)
  then show ?case using stmt_ok.Revert by auto
qed

lemma prf_compat_not_located_stmts:
  assumes "\<Gamma> \<turnstile> Stmts oks \<stileturn> \<Delta>"
      and "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
      and "Stmts stmts_wf"
      and "\<forall>Stmt \<in> set Stmts. stmt_locations Stmt = {#}"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile> Stmts oks \<stileturn> \<Delta>') 
              \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' 
              \<and> loc_ty_env \<Delta>' = loc_ty_env \<Gamma>'"
  using assms
proof (induction Stmts arbitrary: \<Gamma>' \<Gamma> \<Delta>)
  case Nil
  then show ?case by auto
next
  case (Cons Stmt Stmts)
  then obtain \<Delta>' 
    where stmt_ok: "\<Gamma> \<turnstile> Stmt ok \<stileturn> \<Delta>'" 
      and tail_ok: "\<Delta>' \<turnstile> Stmts oks \<stileturn> \<Delta>"
    by auto
  
  have "\<exists>\<Delta>''. (\<Gamma>' \<turnstile> Stmt ok \<stileturn> \<Delta>'') 
              \<and> var_ty_env \<Delta>' = var_ty_env \<Delta>'' 
              \<and> loc_ty_env \<Delta>'' = loc_ty_env \<Gamma>'"
    apply (rule prf_compat_not_located_stmt)
    using stmt_ok apply assumption
    using Cons by auto
  then obtain \<Delta>''
    where "\<Gamma>' \<turnstile> Stmt ok \<stileturn> \<Delta>''" 
      and "var_ty_env \<Delta>' = var_ty_env \<Delta>''" 
      and "loc_ty_env \<Delta>'' = loc_ty_env \<Gamma>'"
    by auto

  have "\<exists>\<Xi>. (\<Delta>'' \<turnstile> Stmts oks \<stileturn> \<Xi>) 
              \<and> var_ty_env \<Delta> = var_ty_env \<Xi> 
              \<and> loc_ty_env \<Xi> = loc_ty_env \<Delta>''"
    apply (rule Cons.IH)
    using tail_ok apply assumption
    using \<open>var_ty_env \<Delta>' = var_ty_env \<Delta>''\<close> apply auto[1]
    using Cons apply auto
    by (metis list.set_intros(1) list.set_intros(2) wf_stmts.elims(3))

  then show ?case using \<open>\<Gamma>' \<turnstile> Stmt ok \<stileturn> \<Delta>''\<close> \<open>loc_ty_env \<Delta>'' = loc_ty_env \<Gamma>'\<close> by auto
qed

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

lemma resourceSub_empty_quant:
  assumes "exactType r = Some (q,t)"
  shows "exactType (r -\<^sub>r r) = Some (empty,t)"
  using assms
  apply (cases r, auto)
  using exactType_has_same_base_type resourceSub_empty_quant_res by auto

lemma empty_offset_lookup_empty: "0\<^sub>\<O> l = []"
  by (auto simp: empty_offset_def)

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

theorem stmts_preservation:
  assumes "\<langle>\<Sigma>, \<S>\<rangle> \<rightarrow> \<langle>\<Sigma>', \<S>'\<rangle>"
      and "\<Gamma> \<turnstile> \<S> oks \<stileturn> \<Delta>"
      and "compat \<Gamma> (build_stmts_offset \<Gamma> \<S>) empty_offset \<Sigma>"
      and "\<S> stmts_wf"
    shows "\<exists>\<Gamma>' \<Delta>'. compat \<Gamma>' (build_stmts_offset \<Gamma>' \<S>') empty_offset \<Sigma>'
                \<and> (\<Gamma>' \<turnstile> \<S>' oks \<stileturn> \<Delta>')
                \<and> var_ty_env \<Delta> = var_ty_env \<Delta>'
                \<and> (\<S>' stmts_wf)"
  using assms
proof(induction arbitrary: \<Gamma> \<Delta>)
  case (EFlowSrcCongr \<Sigma> Src \<Sigma>' Src' Dst)
  then have "\<Gamma> \<turnstile> (Src \<longlonglongrightarrow> Dst) ok \<stileturn> \<Delta>" by simp
  then obtain q r t \<Delta>' 
    where src_ty: "\<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; Src : (q,t) \<stileturn> \<Delta>'" 
      and dst_ty: "\<Delta>' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r,t) \<stileturn> \<Delta>"
    using stmt_ok.simps by auto
  then have typecheck_match_src: "typecheck \<Gamma> s (\<lambda>(_, t). (empty, t)) Src = Some ((q,t), \<Delta>')"
    by (simp add: typecheck_matches_loc_type)
  have "\<not>(located Src)"
    using EFlowSrcCongr.hyps step_not_located by auto
  then have "locations Dst = {#}"
    using EFlowSrcCongr
    by (cases Src, auto)
  then have empty_dst_offset: "build_offset (\<lambda>(r,s). (r \<oplus> q, s)) Dst = 0\<^sub>\<O>"
    by (simp add: no_locations_build_offset_empty)
  have "\<exists>\<Gamma>' \<Delta>''. compat \<Gamma>' (build_offset (\<lambda>(_,t). (empty, t)) Src') empty_offset \<Sigma>'
                 \<and> (\<Gamma>' \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; Src' : (q,t) \<stileturn> \<Delta>'')
                 \<and> var_ty_env \<Delta>' = var_ty_env \<Delta>'' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>'
                 \<and> loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>' \<and> (Src' wf)"
  proof(rule locator_preservation)
    show "< \<Sigma> , Src > \<rightarrow> < \<Sigma>' , Src' >" using EFlowSrcCongr by simp
    show "\<Gamma> \<turnstile>{s} \<lambda>(_, t). (empty, t) ; Src : (q, t) \<stileturn> \<Delta>'" using src_ty by simp
    show "compat \<Gamma> (build_offset (\<lambda>(_, t). (empty, t)) Src) empty_offset \<Sigma>"
      using EFlowSrcCongr.prems(2) empty_dst_offset typecheck_match_src by auto
    show "offset_dom empty_offset \<subseteq> loc_dom \<Gamma>" by simp
    show "type_preserving_offset empty_offset" by (simp add: empty_offset_type_preserving)
    show "type_preserving (\<lambda>(_, t). (TyQuant.empty, t))" by (simp add: type_preserving_with_quant)
    show "Src wf"
      using EFlowSrcCongr.prems(3) stmt_wf_src_wf wf_stmts.simps(2) by blast
  qed
  then obtain \<Gamma>' \<Delta>''
    where compat: "compat \<Gamma>' (build_offset (\<lambda>(_,t). (empty, t)) Src') empty_offset \<Sigma>'"
      and new_src_ty: "\<Gamma>' \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; Src' : (q,t) \<stileturn> \<Delta>''"
      and "var_ty_env \<Delta>' = var_ty_env \<Delta>''"
      and "\<Sigma> \<subseteq>\<^sub>s \<Sigma>'"
      and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
      and "Src' wf"
    by auto
  then have typecheck_match_new_src: "typecheck \<Gamma>' s (\<lambda>(_, t). (empty, t)) Src' = Some ((q,t), \<Delta>'')"
    by (simp add: typecheck_matches_loc_type)
  (* I think this should work out *)
  have "\<exists>\<Delta>'. (\<Delta>'' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r,t) \<stileturn> \<Delta>') 
             \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' \<and> loc_ty_env \<Delta>' = loc_ty_env \<Delta>''"
    apply (rule prf_compat_not_located)
    using dst_ty apply assumption
    using \<open>var_ty_env \<Delta>' = var_ty_env \<Delta>''\<close> EFlowSrcCongr \<open>locations Dst = {#}\<close>
    apply simp
    using EFlowSrcCongr.prems(3) apply auto[1]
    by (simp add: \<open>locations Dst = {#}\<close>)
    
  then obtain \<Xi>' 
    where new_dst_ty: "\<Delta>'' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r,t) \<stileturn> \<Xi>'"
       (* TODO: This part should work out because the var_ty_env of \<Delta>' is the same as \<Delta>'' *)
      and "var_ty_env \<Delta> = var_ty_env \<Xi>'"
      and "loc_ty_env \<Xi>' = loc_ty_env \<Delta>''"
    by auto
  then show ?case
  proof(intro exI conjI)
    show "compat \<Gamma>' (build_stmts_offset \<Gamma>' [Src' \<longlonglongrightarrow> Dst]) empty_offset \<Sigma>'"
      using typecheck_match_new_src
      apply auto
      by (simp add: \<open>locations Dst = {#}\<close> build_offset_no_locs compat)

    show "\<Gamma>' \<turnstile> [Src' \<longlonglongrightarrow> Dst] oks \<stileturn> \<Xi>'" using new_src_ty new_dst_ty
      apply simp
      apply (rule Flow)
      by assumption+

    show "var_ty_env \<Delta> = var_ty_env \<Xi>'" using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>'\<close> by auto

    show "[Src' \<longlonglongrightarrow> Dst] stmts_wf"
      apply (auto simp: \<open>Src' wf\<close> \<open>\<not> located Src\<close>)
      using EFlowSrcCongr.prems(3) apply auto[1]
      using \<open>locations Dst = {#}\<close> by (cases Src', auto)
  qed
next
  case (EFlowDstCongr Src \<Sigma> Dst \<Sigma>' Dst')
  then have "\<Gamma> \<turnstile> (Src \<longlonglongrightarrow> Dst) ok \<stileturn> \<Delta>" by simp
  then obtain q r t \<Delta>'
    where src_ty: "\<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; Src : (q,t) \<stileturn> \<Delta>'" 
      and dst_ty: "\<Delta>' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r,t) \<stileturn> \<Delta>"
    using stmt_ok.simps by auto 
  then have typecheck_match_src: "typecheck \<Gamma> s (\<lambda>(_, t). (empty, t)) Src = Some ((q,t), \<Delta>')"
    by (simp add: typecheck_matches_loc_type)
  obtain \<mu> \<rho> where "\<Sigma> = (\<mu>, \<rho>)" by (cases "\<Sigma>")
  have "\<exists>\<Gamma>' \<Delta>''. compat \<Gamma>' (build_offset (\<lambda>(r,s). (r \<oplus> q, s)) Dst') (build_offset (\<lambda>(_,t). (empty, t)) Src) \<Sigma>'
                 \<and> (\<Gamma>' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst' : (r,t) \<stileturn> \<Delta>'')
                 \<and> var_ty_env \<Delta> = var_ty_env \<Delta>'' \<and> \<Sigma> \<subseteq>\<^sub>s \<Sigma>'
                 \<and> loc_ty_env \<Delta>' \<subseteq>\<^sub>m loc_ty_env \<Gamma>' \<and> (Dst' wf)"
  proof(rule locator_preservation)
    show "< \<Sigma> , Dst > \<rightarrow> < \<Sigma>' , Dst' >" using EFlowDstCongr by simp
    show "\<Delta>' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r, t) \<stileturn> \<Delta>" using dst_ty by simp

    show "compat \<Delta>' (build_offset (\<lambda>(r, s). (r \<oplus> q, s)) Dst) (build_offset (\<lambda>(_,t). (empty, t)) Src) \<Sigma>"
      using EFlowDstCongr typecheck_match_src
      apply auto
    proof -
      assume a1: "compat \<Gamma> (build_offset (\<lambda>(r, y). (r \<oplus> q, y)) Dst \<circ>\<^sub>o build_offset (\<lambda>(_, y). (empty, y)) Src) 0\<^sub>\<O> \<Sigma>"
      assume a2: "located Src"
      have "\<exists>p. case \<Sigma> of (x, xa) \<Rightarrow> p x xa"
        by blast
      then show ?thesis
        using a2 a1 located_env_compat src_ty type_preserving_with_quant by fastforce
    qed
    
    show "offset_dom (build_offset (\<lambda>(_,t). (empty, t)) Src) \<subseteq> loc_dom \<Delta>'"
      using located_locations_in_offset_dom src_ty type_check_loc_dom_same by auto
    show "type_preserving_offset (build_offset (\<lambda>(_,t). (empty, t)) Src)"
      by (simp add: type_preserving_build type_preserving_with_quant)
    show "type_preserving (\<lambda>(r, s). (r \<oplus> q, s))" by (simp add: type_preserving_add)
    show "Dst wf" using EFlowDstCongr by simp
  qed
  then obtain \<Delta>'' and \<Xi>'
    where new_compat: "compat \<Delta>'' (build_offset (\<lambda>(r,s). (r \<oplus> q, s)) Dst') (build_offset (\<lambda>(_,t). (empty, t)) Src) \<Sigma>'"
      and "\<Delta>'' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst' : (r,t) \<stileturn> \<Xi>'"
      and var_env_same: "var_ty_env \<Delta> = var_ty_env \<Xi>'"
      and "\<Sigma> \<subseteq>\<^sub>s \<Sigma>'"
      and loc_ty_env_subset: "loc_ty_env \<Delta>' \<subseteq>\<^sub>m loc_ty_env \<Delta>''"
      and "Dst' wf"
    by auto
  show ?case
  proof(intro exI conjI)
    obtain \<mu>' \<rho>' where "\<Sigma>' = (\<mu>', \<rho>')" by (cases \<Sigma>')
    have new_src_ty: "(temp_update_env \<Gamma> \<Delta>'') \<turnstile>{s} (\<lambda>(_, y). (empty, y)) ; Src : (q,t) \<stileturn> \<Delta>''"
      using EFlowDstCongr.hyps(1) \<open>loc_ty_env \<Delta>' \<subseteq>\<^sub>m loc_ty_env \<Delta>''\<close> located_var_ignore src_ty by auto
    then have "typecheck (temp_update_env \<Gamma> \<Delta>'') s (\<lambda>(_, y). (empty, y)) Src = Some ((q,t), \<Delta>'')"
      by (simp add: typecheck_matches_loc_type)
    then show "compat (temp_update_env \<Gamma> \<Delta>'') (build_stmts_offset (temp_update_env \<Gamma> \<Delta>'') [Src \<longlonglongrightarrow> Dst']) 0\<^sub>\<O> \<Sigma>'"
      using \<open>\<Sigma>' = (\<mu>', \<rho>')\<close>
      apply auto
    proof (rule temp2)
      show updated: "update_locations (temp_update_env \<Gamma> \<Delta>'') (build_offset (\<lambda>(_, y). (empty, y)) Src) = \<Delta>''"
        apply (rule temp1[where \<Delta> = \<Delta>'])
        apply (rule located_env_compat2(2)[symmetric])
        using src_ty apply assumption
        using EFlowDstCongr typecheck_match_src \<open>\<Sigma> = (\<mu>, \<rho>)\<close> apply auto[1]
        using EFlowDstCongr apply auto[1]
        apply (simp add: type_preserving_with_quant)
        using loc_ty_env_subset apply auto[1]
        using located_locations_in_offset_dom src_ty by auto

      then show "compat (update_locations (temp_update_env \<Gamma> \<Delta>'') (build_offset (\<lambda>(_, t). (empty, t)) Src))
         (build_offset (\<lambda>(r, y). (r \<oplus> q, y)) Dst') (build_offset (\<lambda>(_, t). (empty, t)) Src \<circ>\<^sub>o 0\<^sub>\<O>) (\<mu>', \<rho>')"
        using \<open>\<Sigma>' = (\<mu>', \<rho>')\<close> new_compat by auto

      show "type_preserving_offset (build_offset (\<lambda>(_, t). (empty, t)) Src)"
        by (simp add: type_preserving_build type_preserving_with_quant)

      show "type_preserving_offset 0\<^sub>\<O>"
        by (simp add: empty_offset_type_preserving)

      show "offset_dom (build_offset (\<lambda>(_, y). (empty, y)) Src) \<subseteq> loc_dom \<Gamma>"
        using located_locations_in_offset_dom src_ty by auto

      show "temp_update_env \<Gamma> \<Delta>'' = temp_update_env \<Gamma> \<Delta>''" by simp

      show "env_select_loc_compat \<Gamma> 0\<^sub>\<O> \<rho>"
        using EFlowDstCongr.prems(2) \<open>\<Sigma> = (\<mu>, \<rho>)\<close> by auto

      show "\<rho> \<subseteq>\<^sub>m \<rho>'"
        using \<open>\<Sigma> = (\<mu>, \<rho>)\<close> \<open>\<Sigma> \<subseteq>\<^sub>s \<Sigma>'\<close> \<open>\<Sigma>' = (\<mu>', \<rho>')\<close> by auto 
    qed

    show "(temp_update_env \<Gamma> \<Delta>'') \<turnstile> [Src \<longlonglongrightarrow> Dst'] oks \<stileturn> \<Xi>'"
      apply simp
    proof(rule Flow)
      show "(temp_update_env \<Gamma> \<Delta>'') \<turnstile>{s} \<lambda>(_, t). (empty, t) ; Src : (q, t) \<stileturn> \<Delta>''"
        using EFlowDstCongr.hyps(1) \<open>loc_ty_env \<Delta>' \<subseteq>\<^sub>m loc_ty_env \<Delta>''\<close> located_var_ignore src_ty by auto
      show "\<Delta>'' \<turnstile>{d} \<lambda>(r, s). (r \<oplus> q, s) ; Dst' : (r, t) \<stileturn> \<Xi>'"
        by (simp add: \<open>\<Delta>'' \<turnstile>{d} \<lambda>(r, s). (r \<oplus> q, s) ; Dst' : (r, t) \<stileturn> \<Xi>'\<close>)
    qed
    show "var_ty_env \<Delta> = var_ty_env \<Xi>'" using var_env_same by simp
    show "[Src \<longlonglongrightarrow> Dst'] stmts_wf"
      using EFlowDstCongr \<open>Dst' wf\<close> 
      by (cases Src, auto)
  qed
next
  case (EFlowLoc \<rho> l r1 k r2 \<mu>)
  then have compat_simp: "compat \<Gamma> (build_stmts_offset \<Gamma> [S (Loc l) \<longlonglongrightarrow> S (Loc k)]) 0\<^sub>\<O> (\<mu>, \<rho>)"
      and l_res: "\<rho> l = r1" 
      and k_res: "(\<rho>(l := r1 -\<^sub>r r1)) k = r2" 
      and sub_no_err: "r1 -\<^sub>r r1 \<noteq> None"
      and add_no_err: "r2 +\<^sub>r r1 \<noteq> None"
    by auto
  from EFlowLoc have "\<Gamma> \<turnstile> (S (Loc l) \<longlonglongrightarrow> S (Loc k)) ok \<stileturn> \<Delta>" by simp
  then obtain q r t \<Delta>' 
    where src_ty: "\<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; S (Loc l) : (q,t) \<stileturn> \<Delta>'" 
      and dst_ty: "\<Delta>' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; S (Loc k) : (r,t) \<stileturn> \<Delta>"
    using stmt_ok.simps by auto
  have l_in_env: "\<Gamma> (Loc l) = Some (q,t)" using src_ty loc_type.cases by blast
  have k_in_env: "\<Delta>' (Loc k) = Some (r,t)" using dst_ty loc_type.cases by blast

  have mid_env: "\<Delta>' = \<Gamma>(Loc l \<mapsto> (empty, t))" 
    using src_ty loc_type.cases
    apply auto
    apply (erule loc_type.cases)
    by auto

  have r1_ty: "\<exists>a b. exactType r1 = Some (a,b) \<and> a \<sqsubseteq> q \<and> b \<approx> t" 
    using compat_simp l_res l_in_env
    by (auto simp: compat_def env_select_loc_compat_def)
  then obtain r1q r1t 
    where r1_exact_ty: "exactType r1 = Some (r1q, r1t)" and "r1q \<sqsubseteq> q" and "r1t \<approx> t"
    by auto
  have r2_ty: "k \<noteq> l \<Longrightarrow> \<exists>a b. exactType r2 = Some (a,b) \<and> a \<sqsubseteq> r \<and> b \<approx> t" 
    using compat_simp k_res k_in_env mid_env
    by (auto simp: compat_def env_select_loc_compat_def)

  have typecheck_src: "typecheck \<Gamma> s (\<lambda>(_,t). (empty, t)) (S (Loc l)) = Some ((q,t), \<Delta>')"
    using src_ty
    using typecheck_matches_loc_type by blast
  have src_loc_compat: "compat \<Delta>' (build_offset (\<lambda>(r,s). (r \<oplus> q, s)) (S (Loc k))) 
                  (build_offset (\<lambda>(_,t). (empty, t)) (S (Loc l)) \<circ>\<^sub>o 0\<^sub>\<O>) (\<mu>, \<rho>) 
        \<and> \<Delta>' = update_locations \<Gamma> (build_offset (\<lambda>(_,t). (empty, t)) (S (Loc l)))"
    apply (rule located_env_compat)
    using EFlowLoc src_ty type_preserving_with_quant l_in_env
    by auto
  have "compat \<Delta> 0\<^sub>\<O>
                  (build_offset (\<lambda>(r,s). (r \<oplus> q, s)) (S (Loc k))
                   \<circ>\<^sub>o build_offset (\<lambda>(_,t). (empty, t)) (S (Loc l)))
                  (\<mu>, \<rho>)
        \<and> \<Delta> = update_locations \<Delta>' (build_offset (\<lambda>(r,s). (r \<oplus> q, s)) (S (Loc k)))"
    apply (rule located_env_compat)
    using EFlowLoc located_env_compat dst_ty src_loc_compat type_preserving_add
    by auto
  let ?\<Gamma>' = "update_locations \<Gamma> (build_stmts_offset \<Gamma> [S (Loc l) \<longlonglongrightarrow> S (Loc k)])"
  show ?case
  proof(intro exI conjI)
    show "compat ?\<Gamma>' (build_stmts_offset ?\<Gamma>' []) 0\<^sub>\<O> (\<mu>, \<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1))"
    proof(rule compatI)
      show "var_dom ?\<Gamma>' = dom \<mu>" using EFlowLoc compat_elim update_loc_preserve_dom by auto

      show "\<forall>la. la \<notin> dom (\<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1)) \<longrightarrow> la \<notin> ran \<mu>"
        using EFlowLoc compat_elim by auto

      show "var_store_sync ?\<Gamma>' (build_stmts_offset ?\<Gamma>' []) \<mu>"
        using EFlowLoc.prems(2) compat_elim(4) var_store_sync_update by fastforce

      show "inj \<mu>" using EFlowLoc compat_elim by auto

      show "env_select_var_compat ?\<Gamma>' (build_stmts_offset ?\<Gamma>' []) 0\<^sub>\<O> 
                                  (\<mu>, \<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1))"
        using l_in_env
      proof(unfold env_select_var_compat_def)
        fix x q' t' j
        show "case (\<mu>, \<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1)) of
        (\<mu>, \<rho>) \<Rightarrow>
          \<forall>x \<tau> la.
             update_locations \<Gamma> (build_stmts_offset \<Gamma> [S (Loc l) \<longlonglongrightarrow> S (Loc k)]) (V x) = Some \<tau> \<and> \<mu> x = Some la \<longrightarrow>
             (\<exists>\<sigma>. exactType (\<rho> la) = Some \<sigma> \<and>
                  build_stmts_offset (update_locations \<Gamma> (build_stmts_offset \<Gamma> [S (Loc l) \<longlonglongrightarrow> S (Loc k)])) [] \<circ>\<^sub>o
                  0\<^sub>\<O>\<^sup>la[\<sigma>] \<sqsubseteq>\<^sub>\<tau>
                  \<tau>)"
          apply simp
        proof(intro allI impI, auto)
          fix y q' t'
          assume "l = k" and "\<Gamma> (V y) = Some (q', t')" and "\<mu> y = Some k"
          then have "\<exists>q'' t''. exactType r1 = Some (q'', t'') \<and> (empty \<oplus> q, t'') \<sqsubseteq>\<^sub>\<tau> (q', t')"
            using offset_comp_def l_res k_res l_in_env compat_simp
            apply (auto simp: offset_comp_def compat_def)
            apply (drule env_select_var_compat_use_exist[where x = y and l = k and \<tau> = "(q', t')"])
            apply assumption
            apply assumption
            by (simp add: offset_comp_def empty_offset_lookup_empty apply_offset_def)
          then have "q \<sqsubseteq> q'" and "t \<approx> t'"
             apply (metis addQuant.simps(1) less_general_type.simps quant_add_comm)
            using r1_ty apply auto
            by (metis \<open>\<exists>q'' t''. exactType r1 = Some (q'', t'') \<and> (empty \<oplus> q, t'') \<sqsubseteq>\<^sub>\<tau> (q', t')\<close> base_type_compat_sym base_type_compat_trans less_general_type.simps option.sel)
          then show "\<exists>aa ba. exactType (r2 +\<^sub>r r1) = Some (aa, ba) \<and> aa \<sqsubseteq> q' \<and> ba \<approx> t'"
            by (metis \<open>l = k\<close> base_type_compat_trans fun_upd_same k_res less_general_quant_trans r1_ty res_cancel sub_no_err)
        next
          fix y q' t'
          have ty_empty: "exactType (r1 -\<^sub>r r1) = Some (empty, r1t)"
            using l_in_env compat_simp resourceSub_empty_quant r1_exact_ty
            by (auto simp: compat_def env_select_loc_compat_def)
          assume "l \<noteq> k" and "\<Gamma> (V y) = Some (q', t')" and "\<mu> y = Some l"
          then have "\<exists>q'' t''. exactType r1 = Some (q'', t'') \<and> (empty, t'') \<sqsubseteq>\<^sub>\<tau> (q', t')"
            using offset_comp_def l_res l_in_env compat_simp
            apply (auto simp: offset_comp_def compat_def)
            apply (drule env_select_var_compat_use_exist[where x = y and l = l and \<tau> = "(q', t')"])
            apply assumption
            apply assumption
            by (simp add: offset_comp_def empty_offset_lookup_empty apply_offset_def)
          then show "\<exists>aa ba. exactType (r1 -\<^sub>r r1) = Some (aa, ba) \<and> aa \<sqsubseteq> q' \<and> ba \<approx> t'"
            using ty_empty
            apply auto
            by (simp add: resourceSub_empty_quant)
        next
          fix y q' t'
          assume "k \<noteq> l" and "\<Gamma> (V y) = Some (q', t')" and "\<mu> y = Some k"
          then have "(\<exists>aa ba.
            exactType (\<rho> k) = Some (aa, ba) \<and>
            \<lambda>ka. if k = ka then [\<lambda>(r, y). (r \<oplus> q, y)]
                 else []\<^sup>k[\<lambda>k. if l = k then [\<lambda>(_, y). (empty, y)] else []\<^sup>k[(aa, ba)]] \<sqsubseteq>\<^sub>\<tau>
            (q', t'))"
            using compat_simp k_res k_in_env l_in_env mid_env
            apply simp
            apply (drule compat_elim(6))
            apply (auto simp: env_select_var_compat_def)
            by fastforce
          then have "\<exists>a b. exactType r2 = Some (a,b) \<and> a \<oplus> q \<sqsubseteq> q' \<and> b \<approx> t'"
            using k_res k_in_env l_in_env mid_env \<open>k \<noteq> l\<close>
            by (auto simp: apply_offset_def)
          assume "k \<noteq> l" and "\<Gamma> (V y) = Some (q', t')" and "\<mu> y = Some k"
          then have r2_ty: "\<exists>a b. exactType r2 = Some (a,b) \<and> a \<sqsubseteq> r \<and> b \<approx> t" 
            using compat_simp k_res k_in_env mid_env
            by (auto simp: compat_def env_select_loc_compat_def)
          then obtain r2q r2t 
            where r2_exact_ty: "exactType r2 = Some (r2q, r2t)" and "r2q \<sqsubseteq> r" and "r2t \<approx> t"
            by auto
          then have "\<exists>aa ba. exactType (r2 +\<^sub>r r1) = Some (aa, ba)"
            using add_no_err r1_exact_ty res_add_ty_first by blast
          have "\<exists>q. exactType (r2 +\<^sub>r r1) = Some (q, r2t)"
            apply (rule res_add_ty_first)
            using r2_exact_ty r1_exact_ty add_no_err by auto
          then obtain q'' where sum_exact_ty: "exactType (r2 +\<^sub>r r1) = Some (q'', r2t)"
            by auto
          have "q'' \<sqsubseteq> r2q \<oplus> r1q"
            apply (rule exactType_add)
            using r2_exact_ty apply assumption
            using r1_exact_ty apply assumption
            using \<open>r1t \<approx> t\<close> \<open>r2t \<approx> t\<close> base_type_compat_sym base_type_compat_trans apply blast
            using sum_exact_ty by assumption
          then show "\<exists>aa ba. exactType (r2 +\<^sub>r r1) = Some (aa, ba) \<and> aa \<sqsubseteq> q' \<and> ba \<approx> t'"
            by (metis (no_types, hide_lams) \<open>\<exists>a b. exactType r2 = Some (a, b) \<and> a \<oplus> q \<sqsubseteq> q' \<and> b \<approx> t'\<close> \<open>r1q \<sqsubseteq> q\<close> less_general_quant_trans less_general_type.simps less_general_type_refl option.inject quant_add_comm quant_add_lt_left r2_exact_ty sum_exact_ty)
        next
          fix y q' t' j
          assume "j \<noteq> l" and "j \<noteq> k"
            and "\<Gamma> (V y) = Some (q', t')" and "\<mu> y = Some j"
          then have "(\<exists>aa ba.
            exactType (\<rho> j) = Some (aa, ba) \<and>
            foldl (\<circ>) (foldl (\<circ>) id (if k = j then [\<lambda>(r, y). (r \<oplus> q, y)] else []))
             (if l = j then [\<lambda>(_, y). (empty, y)] else []) (aa, ba) \<sqsubseteq>\<^sub>\<tau>
            (q', t'))"
            using compat_simp l_in_env
            apply (auto simp: compat_def env_select_var_compat_def apply_offset_def offset_comp_def empty_offset_def)
            by fastforce
          then show "\<exists>aa ba. exactType (\<rho> j) = Some (aa, ba) \<and> aa \<sqsubseteq> q' \<and> ba \<approx> t'"
            using compat_simp l_in_env
            by (smt \<open>j \<noteq> k\<close> \<open>j \<noteq> l\<close> empty_offset_lookup_empty eq_id_iff foldl_Nil less_general_type.simps)
        qed
      qed

      show "finite (dom (\<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1)))" 
        using EFlowLoc compat_elim by auto

      show "env_select_loc_compat ?\<Gamma>' 0\<^sub>\<O> (\<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1))"
      proof(unfold env_select_loc_compat_def, intro allI impI)
        fix j \<tau>
        assume "update_locations \<Gamma> (build_stmts_offset \<Gamma> [S (Loc l) \<longlonglongrightarrow> S (Loc k)]) (Loc j) = Some \<tau>"
        then show "\<exists>\<sigma>. exactType ((\<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1)) j) = Some \<sigma> \<and> 0\<^sub>\<O>\<^sup>j[\<sigma>] \<sqsubseteq>\<^sub>\<tau> \<tau>"
        proof(auto simp: l_in_env apply_offset_def offset_comp_def empty_offset_def)
          fix q' t'
          assume "\<Gamma> (Loc k) = Some (q', t')" and "\<tau> = (empty \<oplus> q, t')" and "j = k" and "l = k"
          then show "\<exists>a ba. exactType (r2 +\<^sub>r r1) = Some (a, ba) \<and> a \<sqsubseteq> empty \<oplus> q \<and> ba \<approx> t'"
            using l_res k_res l_in_env
            apply auto
            by (metis addQuant.simps(1) quant_add_comm r1_ty res_cancel sub_no_err)
        next
          assume "\<tau> = (empty, t)" and "j = l" and "l \<noteq> k"
          then show "\<exists>a b. exactType (r1 -\<^sub>r r1) = Some (a, b) \<and> a \<sqsubseteq> empty \<and> b \<approx> t"
            using l_res l_in_env
            by (simp add: \<open>r1t \<approx> t\<close> r1_exact_ty resourceSub_empty_quant)
        next
          fix q' t'
          assume "k \<noteq> l"
          then obtain r2q r2t 
            where r2_exact_ty: "exactType r2 = Some (r2q, r2t)" and "r2q \<sqsubseteq> r" and "r2t \<approx> t"
            using r2_ty by auto
          then have "\<exists>aa ba. exactType (r2 +\<^sub>r r1) = Some (aa, ba)"
            using add_no_err r1_exact_ty res_add_ty_first by blast
          then obtain qsum where sum_exact_ty: "exactType (r2 +\<^sub>r r1) = Some (qsum, r2t)"
            using add_no_err r1_exact_ty r2_exact_ty res_add_ty_first by blast
          assume "\<Gamma> (Loc k) = Some (q', t')" and "\<tau> = (q' \<oplus> q, t')" and "k \<noteq> l" and "j = k"
          then show "\<exists>aa ba. exactType (r2 +\<^sub>r r1) = Some (aa, ba) \<and> aa \<sqsubseteq> q' \<oplus> q \<and> ba \<approx> t'"
            using l_res k_res l_in_env k_in_env mid_env add_no_err sum_exact_ty
            apply auto
            thm less_general_quant_trans
            apply (rule less_general_quant_trans)
              apply (rule exactType_add)
            using r2_exact_ty apply assumption
            using r1_exact_ty apply assumption
            using \<open>r1t \<approx> t\<close> \<open>r2t \<approx> t\<close> base_type_compat_sym base_type_compat_trans apply blast
              apply simp
            apply (simp add: \<open>r1q \<sqsubseteq> q\<close> \<open>r2q \<sqsubseteq> r\<close> addQuant_less_general)
            by (simp add: \<open>r2t \<approx> t\<close>)
        next
          fix q' t'
          assume "\<Gamma> (Loc j) = Some (q', t')" and "\<tau> = (q', t')" and "j \<noteq> l" and "j \<noteq> k"
          then show "\<exists>aa ba. exactType (\<rho> j) = Some (aa, ba) \<and> aa \<sqsubseteq> q' \<and> ba \<approx> t'"
            using compat_simp
            apply auto
            apply (drule compat_elim(8))
            by (auto simp: env_select_loc_compat_def)
        qed
      qed

      show "\<forall>la t v. (\<rho>(l := r1 -\<^sub>r r1, k := r2 +\<^sub>r r1)) la = Some (t, v) \<longrightarrow> baseTypeMatches t v"
        apply auto
        using EFlowLoc l_in_env apply (auto simp: apply_offset_def)
        using compat_elim(9) res_cancel apply fastforce
        sorry
    qed
    
    show "?\<Gamma>' \<turnstile> [] oks \<stileturn> ?\<Gamma>'" by simp

    show "var_ty_env \<Delta> = var_ty_env ?\<Gamma>'"
      apply (simp only: update_locations_var_ty_env_id[symmetric])
    proof(rule sym, rule trans)
      show "var_ty_env \<Gamma> = var_ty_env \<Delta>'"
        using located_var_env_same src_ty by auto
      show "var_ty_env \<Delta>' = var_ty_env \<Delta>"
        using located_var_env_same dst_ty by auto
    qed

    show "[] stmts_wf" by simp
  qed
next
  case (EFlowLocFail \<rho> l r1 r2 k \<mu>)
  (* TODO: For this case, we either need to undo the changes to the environment, or relax the Revert rule *)
  then show ?case sorry
next
  case (EFlowEmptyList Dst \<mu> \<rho> \<tau>)
  then obtain q r t \<Delta>' 
    where src_ty: "\<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; [ \<tau>; ] : (q,t) \<stileturn> \<Delta>'"
      and dst_ty: "\<Delta>' \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r, t) \<stileturn> \<Delta>"
    using stmt_ok.simps by auto
  then have "\<Gamma> = \<Delta>'" and "q = empty" and "t = table [] \<tau>"
    using loc_type.cases by blast+
  then show ?case
  proof(intro exI conjI)
    show "compat \<Delta>' (build_stmts_offset \<Delta>' []) empty_offset (\<mu>, \<rho>)"
      using located_env_compat2(1) src_ty EFlowEmptyList
      apply (simp add: \<open>\<Gamma> = \<Delta>'\<close>)
      by (simp add: compat_id)

    show "\<Delta>' \<turnstile> [] oks \<stileturn> \<Delta>'" by simp

    show "var_ty_env \<Delta> = var_ty_env \<Delta>'"
      using \<open>located Dst\<close> dst_ty located_var_env_same by auto

    show "[] stmts_wf" by simp
  qed
next
  case (EFlowConsList Head Tail Dst \<mu> \<rho> \<tau>)
  then show ?case sorry
next
  case (EFlowCopy L Dst l \<rho> \<mu>)

  then obtain q r t
    where src_ty: "\<Gamma> \<turnstile>{s} (\<lambda>(_,t). (empty, t)) ; copy(L) : (q,t) \<stileturn> \<Gamma>"
      and dst_ty: "\<Gamma> \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r, t) \<stileturn> \<Delta>"
    using stmt_ok.simps
    apply auto
    using located.simps(4) located_env_compat type_preserving_with_quant
    sorry

  obtain \<sigma> where copied_ty: "\<Gamma> \<turnstile>{s} id ; L : \<sigma> \<stileturn> \<Gamma>" and "(q,t) = demote \<sigma>"
    apply (rule loc_type.cases)
    using src_ty apply assumption
    by auto
  
  let ?\<Gamma>' = "\<Gamma>(Loc l \<mapsto> (q,t))"
  let ?\<Delta>' = "\<Delta>(Loc l \<mapsto> (empty,t))"
  show ?case
  proof(intro exI conjI)
    show "compat ?\<Gamma>' (build_stmts_offset ?\<Gamma>' [S (Loc l) \<longlonglongrightarrow> Dst]) 0\<^sub>\<O> (\<mu>, \<rho>(l := deepCopy \<rho> L))"
    proof(rule compatI)
      show "var_dom (\<Gamma>(Loc l \<mapsto> (q, t))) = dom \<mu>" using EFlowCopy compat_elim by auto

      show "\<forall>la. la \<notin> dom (\<rho>(l := deepCopy \<rho> L)) \<longrightarrow> la \<notin> ran \<mu>" 
        using EFlowCopy compat_elim by auto

      show "var_store_sync ?\<Gamma>' (build_stmts_offset ?\<Gamma>' [S (Loc l) \<longlonglongrightarrow> Dst]) \<mu>"
        apply (unfold var_store_sync_def)
        apply auto
         apply (metis EFlowCopy.hyps(3) EFlowCopy.prems(2) compat_elim(3) in_var_lookup_in_store)
        sorry

      show "inj \<mu>" using EFlowCopy compat_elim by auto

      show "env_select_var_compat ?\<Gamma>' (build_stmts_offset ?\<Gamma>' [S (Loc l) \<longlonglongrightarrow> Dst]) 0\<^sub>\<O> (\<mu>, \<rho>(l := deepCopy \<rho> L))"
        sorry

      show "finite (dom (\<rho>(l := deepCopy \<rho> L)))" using EFlowCopy compat_elim by auto

      have "\<exists>\<pi>. exactType (deepCopy \<rho> L) = Some \<pi> \<and> \<pi> \<sqsubseteq>\<^sub>\<tau> demote \<sigma>"
        apply (rule deepCopy_makes_demoted)     
        using copied_ty apply assumption
        (* TODO: Same issue as below *)
        sorry
      then show "env_select_loc_compat (\<Gamma>(Loc l \<mapsto> (q, t))) 0\<^sub>\<O> (\<rho>(l := deepCopy \<rho> L))"
        apply (unfold env_select_loc_compat_def)
        apply (intro allI impI)
        sorry

      show "\<forall>la t v. (\<rho>(l := deepCopy \<rho> L)) la = Some (t, v) \<longrightarrow> baseTypeMatches t v"
        apply auto
        (* TODO: we probably have to change the rules to copy things as they become available, 
                 not once Dst is evaluated, otherwise the environments might be out of sync. *)
        sorry
    qed

    have "(\<Gamma>(Loc l \<mapsto> (empty, t))) \<turnstile>{d} (\<lambda>(r,s). (r \<oplus> q, s)) ; Dst : (r, t) \<stileturn> (\<Delta>(Loc l \<mapsto> (empty, t)))"
      using \<open>locations Dst = {#}\<close> dst_ty
      (* TODO: This will work because Dst has no locations in it at all *)
      sorry
    then show "\<Gamma>(Loc l \<mapsto> (q,t)) \<turnstile> [S (Loc l) \<longlonglongrightarrow> Dst] oks \<stileturn> ?\<Delta>'"
      apply auto
      apply (rule Flow)
      apply (rule Loc)
      by auto

    show "var_ty_env \<Delta> = var_ty_env (\<Delta>(Loc l \<mapsto> (empty, t)))" by simp

    show "[S (Loc l) \<longlonglongrightarrow> Dst] stmts_wf" using EFlowCopy by simp
  qed
next
  case (EStmtsCongr \<Sigma> S1 \<Sigma>' \<S>\<^sub>1' \<S>\<^sub>2)
  then obtain \<Delta>' where s1_ok: "\<Gamma> \<turnstile> S1 ok \<stileturn> \<Delta>'" and tail_ok: "\<Delta>' \<turnstile> \<S>\<^sub>2 oks \<stileturn> \<Delta>"
    by auto

  (* TODO: Very annoying to have to repeat everything twice, basically... *)
  have "\<exists>\<Gamma>' \<Delta>''.
           (compat \<Gamma>' (build_stmts_offset \<Gamma>' \<S>\<^sub>1') 0\<^sub>\<O> \<Sigma>') \<and>
           (\<Gamma>' \<turnstile> \<S>\<^sub>1' oks \<stileturn> \<Delta>'') \<and> var_ty_env \<Delta>' = var_ty_env \<Delta>'' \<and> (\<S>\<^sub>1' stmts_wf)"
  proof(rule EStmtsCongr.IH)
    show "\<Gamma> \<turnstile> [S1] oks \<stileturn> \<Delta>'" using s1_ok by simp

    show "compat \<Gamma> (build_stmts_offset \<Gamma> [S1]) 0\<^sub>\<O> \<Sigma>"
      using EStmtsCongr no_locations_build_stmts_offset_is_empty
      by simp

    show "[S1] stmts_wf" using EStmtsCongr by simp
  qed
  then obtain \<Gamma>' \<Delta>''
    where "compat \<Gamma>' (build_stmts_offset \<Gamma>' \<S>\<^sub>1') 0\<^sub>\<O> \<Sigma>'"
      and new_stmts_ok: "\<Gamma>' \<turnstile> \<S>\<^sub>1' oks \<stileturn> \<Delta>''"
      and "var_ty_env \<Delta>' = var_ty_env \<Delta>''"
      and "\<S>\<^sub>1' stmts_wf"
    by auto

  have "\<exists>\<Xi>. (\<Delta>'' \<turnstile> \<S>\<^sub>2 oks \<stileturn> \<Xi>) 
              \<and> var_ty_env \<Delta> = var_ty_env \<Xi> 
              \<and> loc_ty_env \<Xi> = loc_ty_env \<Delta>''"
    apply (rule prf_compat_not_located_stmts)
    using tail_ok apply assumption
    using \<open>var_ty_env \<Delta>' = var_ty_env \<Delta>''\<close> apply auto[1]
    apply (metis EStmtsCongr.prems(3) append_Cons append_Nil stmts_wf_suf_wf)
    using EStmtsCongr.prems(3) by auto
  then obtain \<Xi> where rest_ok: "\<Delta>'' \<turnstile> \<S>\<^sub>2 oks \<stileturn> \<Xi>" and "var_ty_env \<Delta> = var_ty_env \<Xi>"
    by auto

  then show ?case
  proof(intro exI conjI)
    have "build_stmts_offset (foldl typecheck_stmt \<Gamma>' \<S>\<^sub>1') \<S>\<^sub>2 = 0\<^sub>\<O>"
      using EStmtsCongr no_locations_build_stmts_offset_is_empty
      by simp
    then show "compat \<Gamma>' (build_stmts_offset \<Gamma>' (\<S>\<^sub>1' @ \<S>\<^sub>2)) 0\<^sub>\<O> \<Sigma>'"
      by (simp add: \<open>Psamathe.compat \<Gamma>' (build_stmts_offset \<Gamma>' \<S>\<^sub>1') 0\<^sub>\<O> \<Sigma>'\<close>)

    show "\<Gamma>' \<turnstile> \<S>\<^sub>1' @ \<S>\<^sub>2 oks \<stileturn> \<Xi>"
      using new_stmts_ok rest_ok stmt_append_ok by auto 

    show "var_ty_env \<Delta> = var_ty_env \<Xi>"
      using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>\<close> by auto

    show "\<S>\<^sub>1' @ \<S>\<^sub>2 stmts_wf"  
      using \<open>\<S>\<^sub>1' stmts_wf\<close> EStmtsCongr 
      apply (cases \<S>\<^sub>1')
      apply auto
      by (metis EStmtsCongr.prems(3) append_Cons self_append_conv2 stmts_wf_suf_wf)
  qed
qed

end
