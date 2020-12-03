theory Psamathe
  imports Main "HOL-Library.Multiset"
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = natural | boolean 
  | table "string list" "TyQuant \<times> BaseTy"
type_synonym Type = "TyQuant \<times> BaseTy"
datatype Mode = s | d

datatype Val = Num nat | Bool bool | Table "Resource list"
  and Resource = Res "BaseTy \<times> Val" | error
datatype StorageLoc = SLoc nat | Amount nat nat | ResLoc nat Resource
datatype Stored = V string | Loc StorageLoc

datatype Locator = N nat | B bool | S Stored
  | VDef string BaseTy ("var _ : _")
  | EmptyList Type ("[ _ ; ]")
  | ConsList Type "Locator" "Locator" ("[ _ ; _ , _ ]")
  | Copy Locator ("copy'(_')")
datatype Stmt = Flow Locator Locator
datatype Prog = Prog "Stmt list"

type_synonym Env = "(Stored, Type) map"
type_synonym Store = "(string \<rightharpoonup> StorageLoc) \<times> (nat \<rightharpoonup> Resource)"

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

fun demoteBase :: "BaseTy \<Rightarrow> BaseTy" ("demote\<^sub>*") 
  and demote :: "Type \<Rightarrow> Type"  where
  "demote\<^sub>* natural = natural"
| "demote\<^sub>* boolean = boolean"
| "demote\<^sub>* (table keys \<tau>) = table keys (demote \<tau>)"
| "demote (q, t) = (q, demote\<^sub>* t)"

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ ; _ : _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} f ; (N n) : (toQuant(n), natural) \<stileturn> \<Gamma>"
| Bool: "\<Gamma> \<turnstile>{s} f ; (B b) : (any, boolean) \<stileturn> \<Gamma>"
| Var: "\<lbrakk> \<Gamma> (V x) = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (V x)) : \<tau> \<stileturn> (\<Gamma>(V x \<mapsto> f \<tau>))"
| Loc: "\<lbrakk> \<Gamma> (Loc l) = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (Loc l)) : \<tau> \<stileturn> (\<Gamma>(Loc l \<mapsto> f \<tau>))"
(* | Loc: "\<lbrakk> \<Gamma> (Loc l) = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (Loc l)) : \<tau> \<stileturn> \<Gamma>" *)
(* | Loc: "\<lbrakk> \<Gamma> (Loc l) = Some (f(\<tau>)) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (Loc l)) : \<tau> \<stileturn> (\<Gamma>(Loc l \<mapsto> f(\<tau>)))" *)
| VarDef: "\<lbrakk> V x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} f ; (var x : t) : (empty, t) \<stileturn> (\<Gamma>(V x \<mapsto> f(empty, t)))"
| EmptyList: "\<Gamma> \<turnstile>{s} f ; [ \<tau> ; ] : (empty, table [] \<tau>) \<stileturn> \<Gamma>"
| ConsList: "\<lbrakk> \<Gamma> \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta> ;
              \<Delta> \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi> \<rbrakk> 
             \<Longrightarrow> \<Gamma> \<turnstile>{s} f ; [ \<tau> ; \<L>, Tail ] : (one \<oplus> q, table [] \<tau>) \<stileturn> \<Xi>"
| Copy: "\<lbrakk> \<Gamma> \<turnstile>{s} id ; L : \<tau> \<stileturn> \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{s} f ; copy(L) : demote \<tau> \<stileturn> \<Gamma>"

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal natural = Num 0"
| "emptyVal boolean = Bool False"
| "emptyVal (table keys t) = Table []"

fun located :: "Locator \<Rightarrow> bool" where
  "located (S (Loc _)) = True"
| "located [ \<tau> ; ] = True"
| "located [ \<tau> ; Head, Tail ] = (located Head \<and> located Tail)"
| "located _ = False"

fun lookupResource :: "(nat \<rightharpoonup> Resource) \<Rightarrow> nat \<Rightarrow> Resource" where
  "lookupResource \<rho> l = (case \<rho> l of None \<Rightarrow> error | Some r \<Rightarrow> r)"

fun selectLoc :: "(nat, Resource) map \<Rightarrow> StorageLoc \<Rightarrow> Resource" where
  "selectLoc \<rho> (Amount l n) = (case \<rho> l of Some (Res (t,_)) \<Rightarrow> Res (t, Num n) | _ \<Rightarrow> error)"
| "selectLoc \<rho> (ResLoc l r) = 
    (case \<rho> l of 
        Some (Res (t, Table vals)) \<Rightarrow> if r \<in> set vals then Res (t, Table [r]) else error
       | None \<Rightarrow> error)"
| "selectLoc \<rho> (SLoc l) = lookupResource \<rho> l"

fun select :: "Store \<Rightarrow> Stored \<Rightarrow> Resource" where
  "select (\<mu>, \<rho>) (V x) = (case \<mu> x of Some l \<Rightarrow> selectLoc \<rho> l | None \<Rightarrow> error)"
| "select (\<mu>, \<rho>) (Loc l) = selectLoc \<rho> l"

fun freshLoc :: "(nat \<rightharpoonup> Resource) \<Rightarrow> nat" where
  "freshLoc \<rho> = Max (dom \<rho>) + 1"

fun ensureTableExists :: "(nat \<rightharpoonup> Resource) \<Rightarrow> nat \<Rightarrow> BaseTy \<Rightarrow> (nat \<rightharpoonup> Resource)" where
  "ensureTableExists \<rho> l t = (if l \<in> dom \<rho> then \<rho> else \<rho>(l \<mapsto> Res (t, Table [])))"

fun resourceSum :: "Resource \<Rightarrow> Resource \<Rightarrow> Resource" (infix "+\<^sub>r" 50) where
  "(Res (t1, Num n1))    +\<^sub>r (Res (t2, Num n2))    = (if t1 = t2 then Res (t1, Num (n1 + n2)) else error)"
| "(Res (t1, Bool b1))   +\<^sub>r (Res (t2, Bool b2))   = (if t1 = t2 then Res (t1, Bool (b1 \<or> b2)) else error)"
| "(Res (t1, Table vs1)) +\<^sub>r (Res (t2, Table vs2)) = (if t1 = t2 then Res (t1, Table (vs1 @ vs2)) else error)"
| "_ +\<^sub>r _ = error"

fun deepCopy :: "(nat \<rightharpoonup> Resource) \<Rightarrow> Locator \<Rightarrow> Resource" where
  "deepCopy \<rho> (S (Loc k)) = selectLoc \<rho> k"
| "deepCopy \<rho> [\<tau>; ] = Res (table [] \<tau>, Table [])"
| "deepCopy \<rho> [\<tau>; Head, Tail] = 
  (
    case deepCopy \<rho> Tail of
      Res (t, Table rest) \<Rightarrow> Res (t, Table (deepCopy \<rho> Head # rest))
    | _ \<Rightarrow> error
  )"
(* Ignore everything else, we'll only call deepCopy on "located" Locators *)
| "deepCopy \<rho> _ = error"

inductive loc_eval :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> Locator \<Rightarrow> bool"
  ("< _ , _ > \<rightarrow> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> Res (natural, Num n))), S (Loc (Amount l n)) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b))), S (Loc (SLoc l)) >"
| EVar: "\<lbrakk> \<mu> x = Some l \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), S (V x) > \<rightarrow> < (\<mu>, \<rho>), S (Loc l) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<rightarrow> < (\<mu>(x \<mapsto> (SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t))), S (Loc (SLoc l)) >"
| EConsListHeadCongr: "\<lbrakk> < \<Sigma>, \<L> > \<rightarrow> < \<Sigma>', \<L>' > \<rbrakk>
                   \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<rightarrow> < \<Sigma>', [ \<tau> ; \<L>', Tail ] >"
| EConsListTailCongr: "\<lbrakk> located \<L> ; < \<Sigma>, Tail > \<rightarrow> < \<Sigma>', Tail' > \<rbrakk>
              \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<rightarrow> < \<Sigma>', [ \<tau> ; \<L>, Tail' ] >"
| ECopyCongr: "\<lbrakk> <\<Sigma>, L> \<rightarrow> <\<Sigma>', L'> \<rbrakk> \<Longrightarrow> <\<Sigma>, copy(L)> \<rightarrow> <\<Sigma>', copy(L')>"
| ECopyEval: "\<lbrakk> located L; l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> <(\<mu>, \<rho>), copy(L)> \<rightarrow> <(\<mu>, \<rho>(l \<mapsto> deepCopy \<rho> L)), S (Loc (SLoc l))>"

(* TODO: Update when adding new types *)
fun base_type_compat :: "BaseTy \<Rightarrow> BaseTy \<Rightarrow> bool" (infix "\<approx>" 50) where
  "base_type_compat natural natural = True"
| "base_type_compat boolean boolean = True"
| "base_type_compat (table ks1 (q1,t1)) (table ks2 (q2,t2)) = base_type_compat t1 t2"
| "base_type_compat _ _ = False"

lemma base_type_compat_refl:
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
  then obtain q1 t1e and k2 q2 t2e and k3 q3 t3e 
    where "e1 = (q1,t1e)" and "t2 = table k2 (q2,t2e)" and "t3 = table k3 (q3,t3e)"
    (* TODO: Pretty gross, can we improve? *)
    by (metis BaseTy.distinct(4) BaseTy.inject BaseTy.simps(7) base_type_compat.elims(2))
  then show ?case using table by fastforce
qed

fun exact_type :: "Resource \<Rightarrow> Type option" where
  "exact_type (Res (t, Num n)) = Some (toQuant n, t)"
| "exact_type (Res (t, Bool b)) = Some (if b then (one, t) else (empty, t))"
| "exact_type (Res (t, Table vs)) = Some (toQuant (length vs), t)"
| "exact_type error = None"

fun less_general_quant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "less_general_quant q any = True"
| "less_general_quant one r = (r \<in> {one, nonempty})"
| "less_general_quant nonempty r = (r = nonempty)"
| "less_general_quant empty r = (r = empty)"
| "less_general_quant any r = (r = any)"

fun less_general_type :: "Type \<Rightarrow> Type \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>\<tau>" 50) where
  "less_general_type (q,t) (r,u) = (q \<sqsubseteq> r \<and> t = u)"

fun ty_res_compat :: "Type \<Rightarrow> Resource \<Rightarrow> bool" (infix "\<triangleq>" 50) where
  "(q,t1) \<triangleq> (Res (t2,_)) = (t1 \<approx> t2)"
| "_ \<triangleq> error = False"

fun var_dom :: "Env \<Rightarrow> string set" where
  "var_dom \<Gamma> = { x . V x \<in> dom \<Gamma> }"

fun type_less_general :: "Type option \<Rightarrow> Type option \<Rightarrow> bool" (infix "\<preceq>\<^sub>\<tau>" 50) where
  "type_less_general (Some (q,t)) (Some (r,u)) = (q \<sqsubseteq> r \<and> t = u)"
| "type_less_general None None = True"
| "type_less_general _ _ = False"

fun parent :: "StorageLoc \<Rightarrow> nat" where 
  "parent (SLoc l) = l"
| "parent (Amount l _) = l"
| "parent (ResLoc l _) = l"

fun storageLocRefs :: "StorageLoc \<Rightarrow> nat set" where
  "storageLocRefs l = {parent l}"

fun references :: "(string, StorageLoc) map \<Rightarrow> nat set" where
  "references \<mu> = \<Union> (image storageLocRefs (ran \<mu>))"

fun finite_store :: "Store \<Rightarrow> bool" where
  "finite_store (\<mu>, \<rho>) = (finite (dom \<mu>) \<and> finite (dom \<rho>))"

fun locations :: "Locator \<Rightarrow> StorageLoc multiset" where
  "locations (N n) = {#}"
| "locations (B b) = {#}"
| "locations (S (V x)) = {#}"
| "locations (S (Loc l)) = {#l#}"
| "locations (var x : t) = {#}"
 (* NOTE: We consider copy(L) to have no locations, because the locations won't be modified *)
| "locations (copy(L)) = locations L"
| "locations [ \<tau> ; ] = {#}"
| "locations [ \<tau> ; \<L>, Tail ] = (locations \<L> + locations Tail)"

inductive wf_locator :: "Locator \<Rightarrow> bool" ("_ wf" 10) where
  EmptyWf: "[ \<tau> ; ] wf"
| VarWf: "S x wf"
| NatWf: "N n wf"
| BoolWf: "B b wf"
| CopyWf: "\<lbrakk> L wf \<rbrakk> \<Longrightarrow> (copy(L)) wf"
| ConsLocWf: "\<lbrakk> located \<L> ; \<L> wf ; Tail wf \<rbrakk> \<Longrightarrow> [ \<tau> ; \<L>, Tail ] wf"
| ConsNotLocWf: "\<lbrakk> \<not>(located \<L>) ; \<L> wf ; locations Tail = {#}; Tail wf \<rbrakk> \<Longrightarrow> [ \<tau> ; \<L>, Tail ] wf"

fun var_ty_env :: "Env \<Rightarrow> (string \<rightharpoonup> Type)" where
  "var_ty_env \<Gamma> = (\<lambda>x. \<Gamma> (V x))"

fun loc_ty_env :: "Env \<Rightarrow> (StorageLoc \<rightharpoonup> Type)" where
  "loc_ty_env \<Gamma> = (\<lambda>l. \<Gamma> (Loc l))"

fun bind_option :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
  "bind_option f x = (case map_option f x of Some b \<Rightarrow> b | _ \<Rightarrow> None)"

fun lookup_var_loc :: "Env \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> (string \<rightharpoonup> Type)" (infix "\<circ>\<^sub>l" 30) where
  "lookup_var_loc \<Gamma> \<mu> = ((\<lambda>l. \<Gamma> (Loc l)) \<circ>\<^sub>m \<mu>)"

type_synonym Offset = "StorageLoc \<Rightarrow> (Type \<Rightarrow> Type) list" 

definition apply_offset :: "Offset \<Rightarrow> StorageLoc \<Rightarrow> Type \<Rightarrow> Type" ("_\<^sup>_[_]" 110) where
  "apply_offset \<O> l \<equiv> foldl (\<circ>) id (\<O> l)"

nonterminal offset_let

syntax
  "_offset_let" :: "[StorageLoc, Type \<Rightarrow> Type] \<Rightarrow> offset_let" ("_ /@@/ _")
  "_OffsetUpd"  :: "[Offset, offset_let] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)

translations
  "_OffsetUpd \<O> (_offset_let l f)" \<rightharpoonup> "\<O>(l := \<O> l @ [f])"

definition offset_comp :: "Offset \<Rightarrow> Offset \<Rightarrow> Offset" (infixl "\<circ>\<^sub>o" 65) where
  "\<O> \<circ>\<^sub>o \<P> \<equiv> (\<lambda>l. \<O> l @ \<P> l)"

lemma offset_comp_assoc: "(\<O> \<circ>\<^sub>o \<P>) \<circ>\<^sub>o \<Q> = \<O> \<circ>\<^sub>o (\<P> \<circ>\<^sub>o \<Q>)"
  by (auto simp: offset_comp_def)

definition var_store_sync :: "Env \<Rightarrow> Offset \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> bool" where
  "var_store_sync \<Gamma> \<O> \<mu> \<equiv>
      \<forall>x l \<tau>. (\<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau>) \<longrightarrow> \<Gamma> (V x) = Some (\<O>\<^sup>l[\<tau>])"

definition env_select_compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" where
  "env_select_compat \<Gamma> \<Sigma> \<equiv> \<forall>x \<tau>. \<Gamma> x = Some \<tau> \<longrightarrow> ty_res_compat \<tau> (select \<Sigma> x)"

(* NOTE: compat can take a function from Vars/Locs to updaters (default to id) instead of a single function,
          this may let us get rid of some of the issues we face due to the updater changing throughout 
          the rules ... *)
definition compat :: "Env \<Rightarrow> Offset \<Rightarrow> Store \<Rightarrow> bool" where
  "compat \<Gamma> \<O> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> 
                        var_dom \<Gamma> = dom \<mu> \<and>
                        (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>) \<and>
                        var_store_sync \<Gamma> \<O> \<mu> \<and>
                        inj \<mu> \<and> finite (dom \<rho>) \<and>
                        env_select_compat \<Gamma> (\<mu>, \<rho>)"
                        (*(\<forall>x. exact_type (select (\<mu>, \<rho>) x) \<preceq>\<^sub>\<tau> \<Gamma> x))" *)

lemma compat_elim[elim]:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "compat \<Gamma> \<O> (\<mu>, \<rho>)"
  shows "var_dom \<Gamma> = dom \<mu>" 
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>" 
    and "var_store_sync \<Gamma> \<O> \<mu>"
    and "inj \<mu>" 
    and "env_select_compat \<Gamma> (\<mu>, \<rho>)"
    and "finite (dom \<rho>)"
  using assms
  by (auto simp: compat_def)

lemma compatI[intro]:
  assumes "var_dom \<Gamma> = dom \<mu>" 
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>" 
    and "var_store_sync \<Gamma> \<O> \<mu>"
    and "inj \<mu>" 
    and "env_select_compat \<Gamma> (\<mu>, \<rho>)"
    and "finite (dom \<rho>)"
  shows "compat \<Gamma> \<O> (\<mu>, \<rho>)"
  using assms
  by (simp add: compat_def)

lemma in_type_env_select:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)"
      and "x \<in> dom \<Gamma>"
  obtains r where "select (\<mu>, \<rho>) x = Res r"
  using assms
  by (metis Resource.exhaust domD env_select_compat_def ty_res_compat.simps(2))

lemma select_loc_update:
  fixes \<rho> \<rho>' l
  assumes "\<rho> \<subseteq>\<^sub>m \<rho>'" and "selectLoc \<rho> l \<noteq> error"
    shows "selectLoc \<rho> l = selectLoc \<rho>' l"
  using assms
proof(cases l)
  case (SLoc x1)
  then show ?thesis using assms
    apply (cases "\<rho>' x1")
     apply (auto simp: map_le_def)
    apply (metis domIff option.case_eq_if)
    by (metis domIff option.case_eq_if option.sel)
next
  case (Amount k n)
  then obtain temp where "\<rho> k = Some temp" using assms by fastforce
  then obtain r where "\<rho> k = Some (Res r)" using assms Amount
    apply auto
    by (metis Resource.simps(5) exact_type.cases) (* TODO: why is it using exact_type? *)
  then have "\<rho>' k = Some (Res r)" using assms map_le_def domI
    by metis
  then show ?thesis using Amount assms by (simp add: \<open>\<rho> k = Some (Res r)\<close>)
next
  case (ResLoc k r)
  then show ?thesis using assms
    apply (cases "\<rho> k")
    apply (auto simp: map_le_def)
    by force
qed

lemma select_update:
  fixes \<mu> \<rho> \<mu>' \<rho>' x
  assumes "select (\<mu>, \<rho>) x \<noteq> error"
      and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'"
    shows "select (\<mu>, \<rho>) x = select (\<mu>', \<rho>') x"
  using assms
proof (cases x)
  case (V x1)
  then have "select (\<mu>, \<rho>) (V x1) \<noteq> error" using assms by simp
  then obtain l where "\<mu> x1 = Some l" and "selectLoc \<rho> l \<noteq> error" using assms
    by (metis option.case_eq_if option.collapse select.simps(1)) 
  then have "\<mu>' x1 = Some l" using assms
    by (metis domI map_le_def)
  then show ?thesis using assms V
    apply auto
    by (metis \<open>\<mu> x1 = Some l\<close> option.simps(5) select_loc_update)
next
  case (Loc x2)
  then show ?thesis
    apply auto
    by (metis assms(1) assms(3) select.simps(2) select_loc_update)
qed

lemma in_var_env_select:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)"
      and "var_dom \<Gamma> = dom \<mu>"
      and "\<mu> x = Some l" 
  obtains r where "selectLoc \<rho> l = Res r"
  using assms
  apply auto
  by (metis domI in_type_env_select mem_Collect_eq option.simps(5) select.simps(1) that)

lemma in_type_env_compat:
  fixes \<Gamma> \<mu> \<rho> x \<tau>
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" 
    and "var_dom \<Gamma> = dom \<mu>"
    and "\<Gamma> (V x) = Some \<tau>"
  obtains l where "\<mu> x = Some l" and "\<tau> \<triangleq> selectLoc \<rho> l"
  using assms
proof(auto)
  assume "\<Gamma> (V x) = Some \<tau>" and "{x. V x \<in> dom \<Gamma>} = dom \<mu>"
  then have "x \<in> dom \<mu>" by auto
  then obtain l where "\<mu> x = Some l" and "\<tau> \<triangleq> selectLoc \<rho> l" using assms
    apply (auto simp: env_select_compat_def)
    by (metis (full_types) option.simps(5) select.simps(1) surj_pair)
  then show ?thesis using assms that by simp
qed

definition resource_le :: "(nat \<rightharpoonup> Resource) \<Rightarrow> (nat \<rightharpoonup> Resource) \<Rightarrow> bool" (infix "\<subseteq>\<^sub>r" 50) where
  "\<rho> \<subseteq>\<^sub>r \<rho>' \<equiv> \<rho> \<subseteq>\<^sub>m \<rho>' \<and> (\<forall>n \<in> dom \<rho>' - dom \<rho>. \<exists>r. \<rho>' n = Some (Res r))"

definition type_preserving :: "(Type \<Rightarrow> Type) \<Rightarrow> bool" where
  "type_preserving f \<equiv> \<forall>\<tau>. (snd \<tau>) \<approx> (snd (f \<tau>))"

lemma select_loc_le:
  fixes \<rho> \<rho>' l
  assumes "\<rho> \<subseteq>\<^sub>m \<rho>'" and "selectLoc \<rho> l \<noteq> error"
  shows "selectLoc \<rho> l = selectLoc \<rho>' l"
  using assms
  by (simp add: assms(1) select_loc_update)

lemma type_preserving_works:
  fixes f q t r s
  assumes "type_preserving f" and "t \<approx> s"
  obtains q' t' where "f (q,t) = (q', t')" and "t' \<approx> s"
  using assms
  apply (auto simp: type_preserving_def)
  using base_type_compat_sym base_type_compat_trans prod.exhaust_sel by blast

lemma select_loc_preserve_var:
  fixes \<Gamma> \<mu> \<rho> \<rho>' x l
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" 
    and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "V x \<in> dom \<Gamma>" and "\<mu> x = Some l"
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>"
  shows "selectLoc \<rho> l = selectLoc \<rho>' l"
  using assms
  apply (cases l)
  apply (metis Resource.distinct(1) in_type_env_select option.simps(5) select.simps(1) select_loc_update)
  apply (metis Resource.distinct(1) in_type_env_select option.simps(5) select.simps(1) select_loc_update)
  by (metis Resource.distinct(1) in_type_env_select option.simps(5) select.simps(1) select_loc_update)

lemma compat_loc_in_env:
  fixes \<Gamma> \<mu> \<rho> l
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "Loc l \<in> dom \<Gamma>"
  obtains r where "selectLoc \<rho> l = Res r"
  using assms
  by (metis in_type_env_select select.simps(2))

lemma select_loc_preserve_loc:
  fixes \<Gamma> \<mu> \<rho> \<rho>' l
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "Loc l \<in> dom \<Gamma>"
  shows "selectLoc \<rho> l = selectLoc \<rho>' l"
  using assms
  by (metis Resource.distinct(1) compat_loc_in_env select_loc_update)

lemma select_preserve:
  fixes \<Gamma> \<mu> \<rho> \<mu>' \<rho>' x
  assumes "compat \<Gamma> \<O> (\<mu>, \<rho>)" and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "x \<in> dom \<Gamma>"
  shows "select (\<mu>, \<rho>) x = select (\<mu>', \<rho>') x"
  using assms
proof(cases x)
  case (V x1)
  then have "x1 \<in> dom \<mu>" using assms by (auto simp: compat_def)
  then have "\<mu> x1 = \<mu>' x1" using assms by (simp add: map_le_def)
  then show ?thesis using assms V \<open>x1 \<in> dom \<mu>\<close>
    apply auto
    by (metis assms(4) compat_elim(2) compat_elim(5) option.simps(5) select_loc_preserve_var)
next
  case (Loc x2)
  then show ?thesis using assms
    apply (simp only: select.simps)
    using compat_elim(5) select_loc_preserve_loc by blast
qed

lemma select_preserve2:
  fixes \<Gamma> \<mu> \<rho> \<mu>' \<rho>' x
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "x \<in> dom \<Gamma>"
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>"
  shows "select (\<mu>, \<rho>) x = select (\<mu>', \<rho>') x"
  using assms
proof(cases x)
  case (V x1)
  then have "x1 \<in> dom \<mu>" using assms
    by (metis Resource.distinct(1) domIff in_type_env_select option.simps(4) select.simps(1)) 
  then have "\<mu> x1 = \<mu>' x1" using assms by (simp add: map_le_def)
  then show ?thesis using assms V \<open>x1 \<in> dom \<mu>\<close>
    apply auto
    by (metis assms(4) assms(5) option.simps(5) select_loc_preserve_var)
next
  case (Loc x2)
  then show ?thesis using assms
    apply (simp only: select.simps)
    using compat_elim(5) select_loc_preserve_loc by blast
qed

lemma not_err_in_dom:
  fixes \<rho> l k
  assumes "selectLoc \<rho> l \<noteq> error" and "k \<in> storageLocRefs l"
  shows "k \<in> dom \<rho>"
proof(cases l)
  case (SLoc j)
  then show ?thesis using assms by (cases "\<rho> j", auto)
next
  case (Amount j n)
  then show ?thesis using assms by (cases "\<rho> j", auto)
next
  case (ResLoc j r)
  then show ?thesis using assms by (cases "\<rho> j", auto)
qed

lemma fresh_loc_not_in_env:
  fixes \<Gamma> \<mu> \<rho> l k j
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "k \<in> storageLocRefs l" and "k \<notin> dom \<rho>"
  shows "Loc l \<notin> dom \<Gamma>"
  using assms compat_loc_in_env not_err_in_dom
  apply auto
  by (metis Resource.distinct(1) assms(3) domI)

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

lemma compat_transfer_var_sync:
  assumes "compat \<Gamma> \<O> (\<mu>, \<rho>)" 
      and "var_store_sync \<Gamma> \<O>' \<mu>"
    shows "compat \<Gamma> \<O>' (\<mu>, \<rho>)"
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

definition idempotent :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "idempotent f \<equiv> f = f \<circ> f"

lemma type_preserving_ty_res_compat:
  assumes "\<tau> \<triangleq> r" and "type_preserving f"
  shows "f \<tau> \<triangleq> r"
  using assms
  apply (auto simp: type_preserving_def)
  by (metis assms(2) ty_res_compat.elims(2) ty_res_compat.simps(1) type_preserving_works)

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

fun update_locations :: "Env \<Rightarrow> Offset \<Rightarrow> Env" where
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

definition insert_many :: "Offset \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> Offset" where
  "insert_many \<O> f \<LL> \<equiv> (\<lambda>l. \<O> l @ replicate (count \<LL> l) f)"

definition offset_of :: "(Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> Offset" where
  "offset_of \<equiv> insert_many (\<lambda>l. [])"

lemma offset_of_add: "offset_of f (\<LL> + \<KK>) = insert_many (offset_of f \<LL>) f \<KK>"
  by (auto simp: insert_many_def offset_of_def replicate_add)

lemma update_locations_step: 
  assumes "\<Gamma>(Loc l) = Some \<tau>" 
  shows "(\<lambda>a. if a = Loc l then Some (f \<tau>) else \<Gamma> a) = update_locations \<Gamma> (\<lambda>a. if l = a then [f] else [])"
proof(rule ext)
  fix x
  show "(\<lambda>a. if a = Loc l then Some (f \<tau>) else \<Gamma> a) x = update_locations \<Gamma> (\<lambda>a. if l = a then [f] else []) x" 
    using assms
    apply (cases x)
    by (auto simp: offset_of_def insert_many_def apply_offset_def option.map_id)
qed

lemma insert_many_single[simp]: 
  "insert_many \<O> f (add_mset l \<LL>) = insert_many (\<O>(l @@ f)) f \<LL>"
  by (auto simp: insert_many_def)

lemma insert_many_id[simp]: "insert_many \<O> f {#} = \<O>"
  by (auto simp: insert_many_def)

lemma insert_many_add: "insert_many \<O> f (\<LL> + \<KK>) = insert_many (insert_many \<O> f \<LL>) f \<KK>"
proof(rule ext)
  fix x
  show "insert_many \<O> f (\<LL> + \<KK>) x = insert_many (insert_many \<O> f \<LL>) f \<KK> x"
    apply (cases x)
    by (auto simp: insert_many_def replicate_add)
qed

lemma update_comm: "update_locations (update_locations \<Gamma> (offset_of f \<LL>)) (offset_of f \<K>) 
       = update_locations \<Gamma> (insert_many (offset_of f \<LL>) f \<K>)"
proof(rule ext)
  fix x
  show "update_locations (update_locations \<Gamma> (offset_of f \<LL>)) (offset_of f \<K>) x =
         update_locations \<Gamma> (insert_many (offset_of f \<LL>) f \<K>) x"
    apply (cases x)
     apply (auto simp: insert_many_def apply_offset_def offset_of_def)
    apply (cases "\<Gamma> x")
    apply auto
    by (metis append_replicate_commute foldl_append foldl_comp)
qed

definition empty_offset :: "Offset" where
  "empty_offset \<equiv> (\<lambda>l. [])"

lemma empty_offset_id: "empty_offset\<^sup>l[\<tau>] = \<tau>"
  by (auto simp: empty_offset_def apply_offset_def)

lemma offset_comp_single: "\<O> \<circ>\<^sub>o (\<lambda>k. if l = k then [f] else []) = \<O>(l @@ f)"
  by (auto simp: offset_comp_def)

lemma offset_comp_empty_r[simp]: "\<O> \<circ>\<^sub>o empty_offset = \<O>"
  by (auto simp: offset_comp_def empty_offset_def)

lemma offset_comp_empty_l[simp]: "empty_offset \<circ>\<^sub>o \<O> = \<O>"
  by (auto simp: offset_comp_def empty_offset_def)

lemma update_loc_empty[simp]: "update_locations \<Gamma> empty_offset = \<Gamma>"
  apply (auto simp: empty_offset_def)
  by (simp add: update_locations_id)

fun build_offset :: "(Type \<Rightarrow> Type) \<Rightarrow> Locator \<Rightarrow> Offset" where
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

lemma empty_offset_apply[simp]: "empty_offset\<^sup>l[\<tau>] = \<tau>"
  by (auto simp: empty_offset_def apply_offset_def)

lemma build_offset_apply_id[simp]: "(build_offset id L)\<^sup>l[\<tau>] = \<tau>"
  apply (induction L, auto)
proof -
  fix x
  show "build_offset (\<lambda>a. a) (S x)\<^sup>l[\<tau>] = \<tau>"
    apply (cases x, auto simp: apply_offset_def)
    using apply_offset_def empty_offset_apply by auto
qed

lemma located_env_compat:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f \<L>) (\<mu>, \<rho>)"
      and "located \<L>"
      and "type_preserving f"
    shows "compat \<Delta> \<O> (\<mu>, \<rho>) \<and> \<Delta> = update_locations \<Gamma> (build_offset f \<L>)"
  using assms
proof(induction arbitrary: \<mu> \<rho> \<O> rule: loc_type.induct)
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
  then show ?case
  proof(cases "\<exists>x. \<mu> x = Some l")
    case True
    then obtain x where "\<mu> x = Some l" ..
    then show ?thesis using Loc
      apply (unfold compat_def, clarsimp, safe)
        apply (simp add: var_store_sync_add offset_comp_single)
      
      apply (smt env_select_compat_def fun_upd_apply option.inject type_preserving_ty_res_compat)
      by (simp add: update_locations_step)
  next
    case False
    then show ?thesis using Loc
      apply (unfold compat_def, clarsimp, safe)
      apply (simp add: var_store_sync_add offset_comp_single)
      apply (smt env_select_compat_def fun_upd_apply option.inject type_preserving_ty_res_compat)
      by (simp add: update_locations_step)
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
        and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f Tail \<circ>\<^sub>o build_offset f \<L>) (\<mu>, \<rho>)"
        apply simp  
    using ConsList.prems(2) apply auto[1]
    using ConsList.prems(1) apply auto[1]
    using ConsList
    by (smt apply_offset_distrib compat_elim(3) compat_transfer_var_sync var_store_sync_def)
  then have "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset f Tail) (\<mu>, \<rho>)" and "\<Delta> = update_locations \<Gamma> (build_offset f \<L>)" 
    using ConsList by auto
  then show "compat \<Xi> \<O> (\<mu>, \<rho>) \<and> \<Xi> = update_locations \<Gamma> (build_offset f [\<tau>; \<L>, Tail])" 
    apply auto
    using ConsList.IH(2) ConsList.prems(3) \<open>located Tail\<close> apply auto[1]
    using ConsList.IH(2) ConsList.prems(3) \<open>located Tail\<close> update_locations_union by auto
next
  case (Copy \<Gamma> L \<tau> f)
  then show ?case by simp
qed

(* TODO: Clean up this and the other version *)
lemma located_env_compat2:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f \<L>) (\<mu>, \<rho>)"
      and "located \<L>"
      and "type_preserving f"
    shows "compat \<Delta> \<O> (\<mu>, \<rho>)" and "\<Delta> = update_locations \<Gamma> (build_offset f \<L>)"
  using assms
  using located_env_compat apply auto[1]
  using assms(1) assms(2) assms(3) assms(4) located_env_compat by auto

lemma comp_id_nop: "foldl (\<circ>) f (replicate n id) = f"
  by (induction n, auto)

lemma insert_many_ids: "(insert_many \<O> id \<LL>)\<^sup>l[\<tau>] = (\<O>\<^sup>l[\<tau>])"
  by (auto simp: insert_many_def apply_offset_def comp_id_nop)

lemma var_store_sync_id_insert:
  assumes "var_store_sync \<Gamma> \<O> \<Sigma>"
  shows "var_store_sync \<Gamma> (insert_many \<O> id \<LL>) \<Sigma>"
  using assms
  by (auto simp: var_store_sync_def insert_many_ids)

lemma var_store_sync_build_id:
  assumes "var_store_sync \<Gamma> \<O> \<Sigma>"
  shows "var_store_sync \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) \<Sigma>"
  using assms
  by (auto simp: var_store_sync_def)

lemma locator_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f \<L>) (\<mu>, \<rho>)"
      and "\<L> wf"
      and "finite (dom \<rho>)"
      and "type_preserving f"
  shows "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. <(\<mu>, \<rho>), \<L>> \<rightarrow> <(\<mu>', \<rho>'), \<L>'> )"
  using assms
proof(induction arbitrary: \<mu> \<rho> m \<O> rule: loc_type.induct)
  case (Nat \<Gamma> f n)
  then show ?case by (meson ENat gen_loc)
next
  case (Bool \<Gamma> f b)
  then show ?case by (meson EBool gen_loc)
next
  case (Var \<Gamma> x \<tau> m f)
  then obtain k where in_lookup: "\<mu> x = Some k" using Var in_type_env_compat
    by (meson compat_elim(1) compat_elim(5))
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
  then have env_compat: "compat \<Gamma> \<O> (\<mu>, \<rho>)" by simp
  have not_in_lookup: "x \<notin> dom \<mu>" using VarDef by (auto simp: compat_def)
  have "finite (dom \<rho>)" using VarDef by simp
  then obtain l where has_loc: "l \<notin> dom \<rho>" using gen_loc env_compat not_in_lookup by blast
  show ?case
  proof(intro disjI2 exI)
    from not_in_lookup and has_loc
    show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> SLoc l), \<rho>(l \<mapsto> Res (t, emptyVal t))) , S (Loc (SLoc l)) >"
      by (rule EVarDef)
  qed
next
  case (EmptyList \<Gamma> f t)
  then show ?case by simp
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have env_compat: "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset f Tail \<circ>\<^sub>o build_offset f \<L>) (\<mu>, \<rho>)"
    by (simp add: offset_comp_assoc)

  from ConsList and wf_locator.cases 
  have "\<L> wf" and "Tail wf" and "finite (dom \<rho>)" and "type_preserving f" by fastforce+

  from this and env_compat 
  have loc_induct: "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. < (\<mu>, \<rho>) , \<L> > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >)"
    and tail_induct: "\<And>\<mu>' \<rho>'. \<lbrakk>compat \<Delta> (\<O> \<circ>\<^sub>o build_offset f Tail) (\<mu>, \<rho>)\<rbrakk>
                         \<Longrightarrow> located Tail \<or> (\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >)"
    apply (simp add: ConsList.IH(1) insert_many_add union_commute)
    by (simp add: ConsList.IH(2) ConsList.prems(4) \<open>Tail wf\<close> \<open>finite (dom \<rho>)\<close>)
   
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
      from loc_l have "compat \<Delta> (\<O> \<circ>\<^sub>o build_offset f Tail) (\<mu>, \<rho>)" 
        using located_env_compat ConsList env_compat
        by (smt add.commute insert_many_add)
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
  then have "L wf" using wf_locator.cases by blast

  then have "compat \<Gamma> \<O> (\<mu>, \<rho>)" using Copy by simp
  then have "compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) (\<mu>, \<rho>)"
    using compat_elim(3) compat_transfer_var_sync var_store_sync_build_id by blast

  have "type_preserving id" by (auto simp: type_preserving_def base_type_compat_refl)

  then have ih: "located L \<or> (\<exists>\<mu>' \<rho>' a. <(\<mu>, \<rho>) , L> \<rightarrow> <(\<mu>', \<rho>') , a>)"
    using Copy.IH \<open>L wf\<close> \<open>Psamathe.compat \<Gamma> (\<O> \<circ>\<^sub>o build_offset id L) (\<mu>, \<rho>)\<close> compat_elim(6) by blast

  obtain l where "l \<notin> dom \<rho>" using Copy.prems(3) gen_loc by auto 
    
  then show ?case
  proof(cases "located L")
    case True
    then show ?thesis
    proof(intro disjI2 exI)
      show "<(\<mu>, \<rho>), copy(L)> \<rightarrow> <(\<mu>, \<rho>(l \<mapsto> deepCopy \<rho> L)), S (Loc (SLoc l))>"
        by (simp add: ECopyEval True \<open>l \<notin> dom \<rho>\<close>)
    qed
  next
    case False
    then show ?thesis using ih using ECopyCongr by blast
  qed
qed

definition offset_dom :: "Offset \<Rightarrow> StorageLoc set" where
  "offset_dom \<O> \<equiv> {l. \<exists>\<tau>. (\<O>\<^sup>l[\<tau>]) \<noteq> \<tau>}"

lemma not_in_offset_dom_is_id:
  assumes "l \<notin> offset_dom \<O>"
  shows "\<O>\<^sup>l[\<tau>] = \<tau>"
  using assms
  apply (auto simp: offset_dom_def apply_offset_def)
  by (metis prod.collapse)

lemma exact_type_preserves_tyquant:
  shows "\<exists>q. exact_type (Res (t, v)) = Some (q, t)"
  by (cases v, auto)

lemma subtype_base_type_compat:
  assumes "\<tau> \<triangleq> r" and "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>"
  shows "\<sigma> \<triangleq> r"
  using assms
  by (metis less_general_type.elims(2) ty_res_compat.elims(2) ty_res_compat.simps(1))

fun valid_ref :: "StorageLoc \<Rightarrow> Resource \<Rightarrow> bool" where
  "valid_ref (SLoc _) (Res _) = True"
| "valid_ref (Amount _ n) (Res (_, Num _)) = True"
| "valid_ref (ResLoc _ v) (Res (_, Table vals)) = (v \<in> set vals)"
| "valid_ref _ _ = False"

(* TODO: Can we use this one to subsume add_fresh_num? *)
lemma add_fresh_loc:
  assumes "compat \<Gamma> \<O> (\<mu>, \<rho>)"
      and "offset_dom \<O> \<subseteq> { l . Loc l \<in> dom \<Gamma> }"
      and "Loc l \<notin> dom \<Gamma>"
      and "parent l \<notin> dom \<rho>"
      and "exact_type (Res (t, v)) = Some \<tau>"
      and "valid_ref l (Res (t, v))"
      and "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>"
    shows "compat (\<Gamma>(Loc l \<mapsto> \<sigma>)) \<O> (\<mu>, \<rho>(parent l \<mapsto> Res (t, v)))"
proof(rule compatI)
  show "var_dom (\<Gamma>(Loc l \<mapsto> \<sigma>)) = dom \<mu>" 
    using assms compat_elim by auto

  show "\<forall>la. la \<notin> dom (\<rho>(parent l \<mapsto> Res (t, v))) \<longrightarrow> la \<notin> references \<mu>"
    using assms compat_elim by auto

  show "var_store_sync (\<Gamma>(Loc l \<mapsto> \<sigma>)) \<O> \<mu>"
    using assms
    apply (auto simp: compat_def var_store_sync_def)
  proof -
    fix x \<tau>
    have "parent l \<notin> references \<mu>"
      using assms(1) assms(4) compat_elim(2) by auto
    assume "\<mu> x = Some l"
    then have "parent l \<in> references \<mu>"
      apply auto
      using ranI by force
    then show "\<Gamma> (V x) = Some (\<O>\<^sup>l[\<tau>])" using \<open>parent l \<notin> references \<mu>\<close>
      by simp
  qed

  show "inj \<mu>" using assms compat_elim by auto

  show "env_select_compat (\<Gamma>(Loc l \<mapsto> \<sigma>)) (\<mu>, \<rho>(parent l \<mapsto> Res (t, v)))"
    using assms
    apply (auto simp: env_select_compat_def)
    apply (cases l, auto)
    apply (metis base_type_compat_refl exact_type_preserves_tyquant less_general_type.simps option.inject)
      apply (metis base_type_compat_refl exact_type_preserves_tyquant less_general_type.simps option.inject)
    apply (cases v, auto)
    apply (simp add: base_type_compat_refl)
    by (metis (mono_tags, lifting) compat_elim(5) domIff env_select_compat_def fun_upd_triv map_le_imp_upd_le map_le_refl option.discI select_preserve)

  show "finite (dom (\<rho>(parent l \<mapsto> Res (t, v))))"
    using assms compat_elim by auto
qed

lemma ty_quant_less_refl: "q \<sqsubseteq> q"
  by (metis TyQuant.exhaust insertI1 less_general_quant.simps(1) less_general_quant.simps(3) less_general_quant.simps(7) less_general_quant.simps(8))
  

lemma add_fresh_num:
  assumes "compat \<Gamma> \<O> (\<mu>, \<rho>)"
      and "offset_dom \<O> \<subseteq> { l . Loc l \<in> dom \<Gamma> }"
      and "Loc (Amount l n) \<notin> dom \<Gamma>"
      and "l \<notin> dom \<rho>"
      and "exact_type (Res (t, Num n)) = Some \<tau>"
    shows "compat (\<Gamma>(Loc (Amount l n) \<mapsto> \<tau>)) \<O> (\<mu>, \<rho>(l \<mapsto> Res (t, Num n)))"
proof -
  have "compat (\<Gamma>(Loc (Amount l n) \<mapsto> \<tau>)) \<O> (\<mu>, \<rho>(parent (Amount l n) \<mapsto> Res (t, Num n)))"
    apply (rule add_fresh_loc)
    using assms apply auto
    by (simp add: ty_quant_less_refl)

  then show "compat (\<Gamma>(Loc (Amount l n) \<mapsto> \<tau>)) \<O> (\<mu>, \<rho>(l \<mapsto> Res (t, Num n)))"
    by simp
qed

definition var_loc_compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" where
  "var_loc_compat \<Gamma> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> 
      \<forall>x l. \<mu> x = Some l \<and> Loc l \<in> dom \<Gamma> \<and> V x \<in> dom \<Gamma> \<longrightarrow> \<Gamma> (Loc l) = \<Gamma> (V x)"

lemma typecheck_id_env_same_source:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>" and "f = id" amd "m = s"
  shows "\<Gamma> = \<Delta>"
  using assms
  by (induction, auto)

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
  then have "\<L> wf" and "Tail wf"
    apply auto 
    apply (erule wf_locator.cases)
    apply auto
    apply (erule wf_locator.cases)
    by auto
  then obtain \<Delta>' where "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" and "var_ty_env \<Delta> = var_ty_env \<Delta>'" 
    using ConsList by auto
  then obtain \<Xi>' where "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'" and "var_ty_env \<Xi> = var_ty_env \<Xi>'"
    using ConsList \<open> Tail wf \<close>
    by auto
  then show ?case using ConsList loc_type.ConsList
    apply auto
    by (metis \<open>Tail wf\<close> \<open>\<L> wf\<close> loc_type.ConsList)
next
  case (Copy \<Gamma> L \<tau> f)
  then have "L wf" using wf_locator.cases by blast
  then have "(\<Gamma>' \<turnstile>{s} id ; L : \<tau> \<stileturn> \<Gamma>') \<and> var_ty_env \<Gamma> = var_ty_env \<Gamma>' \<and> loc_ty_env \<Gamma>' = loc_ty_env \<Gamma>'"
    using Copy typecheck_id_env_same_source
    by (metis locations.simps(6))
  then show ?case using loc_type.Copy by blast 
qed

lemma var_loc_compat_upd:
  assumes "var_loc_compat \<Gamma> (\<mu>, \<rho>)"
      and "\<mu> x = Some l"
      and "inj \<mu>"
    shows "var_loc_compat (\<Gamma>(V x \<mapsto> \<tau>, Loc l \<mapsto> \<tau>)) (\<mu>, \<rho>)"
  using assms
  apply (auto simp: var_loc_compat_def)
  by (simp add: injD)

lemma step_not_located:
  assumes "<\<Sigma>, L> \<rightarrow> <\<Sigma>', L'>"
  shows "\<not>(located L)"
  using assms
  by (induction, auto)

lemma head_step_wf:
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "[\<tau>; \<L>, Tail] wf"
    shows "locations Tail = {#}" and "Tail wf"
  using assms
  apply (metis Locator.distinct(17) Locator.distinct(23) Locator.distinct(9) Locator.inject(6) located.simps(2) located.simps(3) step_not_located wf_locator.simps)
  using assms(2) wf_locator.cases by fastforce

fun temp_update_env :: "Env \<Rightarrow> Env \<Rightarrow> Env" where
  "temp_update_env \<Gamma> \<Delta> (V x) = \<Delta> (V x)"
| "temp_update_env \<Gamma> \<Delta> (Loc l) = (if Loc l \<in> dom \<Gamma> then \<Gamma> (Loc l) else \<Delta> (Loc l))"

lemma update_loc_preserve_dom: "dom \<Gamma> = dom (update_locations \<Gamma> f \<LL>)"
proof
  show "dom \<Gamma> \<subseteq> dom (update_locations \<Gamma> f \<LL>)"
  proof
    fix x
    assume "x \<in> dom \<Gamma>"
    then show "x \<in> dom (update_locations \<Gamma> f \<LL>)"
      apply (cases x)
      by auto
  qed
  show "dom (update_locations \<Gamma> f \<LL>) \<subseteq> dom \<Gamma>"
  proof
    fix x
    assume "x \<in> dom (update_locations \<Gamma> f \<LL>)"
    then show "x \<in> dom \<Gamma>"
      apply (cases x)
      by auto
  qed
qed

lemma temp1:
  assumes "update_locations \<Gamma> f \<LL> = \<Delta>" 
      and "loc_ty_env \<Delta> \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
      and "set_mset \<LL> \<subseteq> dom (loc_ty_env \<Gamma>)"
  shows "update_locations (temp_update_env \<Gamma> \<Delta>') f \<LL> = \<Delta>'"
proof(rule ext)
  fix x
  show "update_locations (temp_update_env \<Gamma> \<Delta>') f \<LL> x = \<Delta>' x"
    apply (cases x, simp, simp)
    using assms
    apply simp
    apply (cases "x \<in> dom \<Gamma>")
     apply simp_all
  proof -
    fix k

    show "\<lbrakk>x = Loc k; update_locations \<Gamma> f \<LL> = \<Delta>; (\<lambda>l. \<Delta> (Loc l)) \<subseteq>\<^sub>m (\<lambda>l. \<Delta>' (Loc l));
           set_mset \<LL> \<subseteq> dom (\<lambda>l. \<Gamma> (Loc l)); Loc k \<in> dom \<Gamma>\<rbrakk>
          \<Longrightarrow> map_option (f ^^ count \<LL> k) (\<Gamma> (Loc k)) = \<Delta>' (Loc k)"
    proof -
      assume "Loc k \<in> dom \<Gamma>"
      then obtain \<tau> where "\<Gamma> (Loc k) = Some \<tau>"
        by auto
      have "update_locations \<Gamma> f \<LL> (Loc k) = \<Delta> (Loc k)"
        by (simp add: assms(1))
      then obtain \<sigma> where "\<Delta> (Loc k) = Some \<sigma>"
        by (metis \<open>Loc k \<in> dom \<Gamma>\<close> domD update_loc_preserve_dom)
      then have "\<Delta>' (Loc k) = Some \<sigma>"
        by (metis (no_types, hide_lams) assms(2) insert_dom insert_iff loc_ty_env.simps map_le_def)
      then have "update_locations \<Gamma> f \<LL> (Loc k) = \<Delta>' (Loc k)" 
        using \<open>\<Delta> (Loc k) = Some \<sigma>\<close> \<open>update_locations \<Gamma> f \<LL> (Loc k) = \<Delta> (Loc k)\<close>
        by simp
      then show ?thesis by auto
    qed

    show "\<lbrakk>x = Loc k; update_locations \<Gamma> f \<LL> = \<Delta>; (\<lambda>l. \<Delta> (Loc l)) \<subseteq>\<^sub>m (\<lambda>l. \<Delta>' (Loc l));
           set_mset \<LL> \<subseteq> dom (\<lambda>l. \<Gamma> (Loc l)); Loc k \<notin> dom \<Gamma>\<rbrakk>
          \<Longrightarrow> map_option (f ^^ count \<LL> k) (\<Delta>' (Loc k)) = \<Delta>' (Loc k)"
    proof -
      assume "set_mset \<LL> \<subseteq> dom (\<lambda>l. \<Gamma> (Loc l))"
         and "update_locations \<Gamma> f \<LL> = \<Delta>"
         and "Loc k \<notin> dom \<Gamma>" 
      then have "k \<notin># \<LL>"
        by auto
      then have "count \<LL> k = 0"
        by (meson count_inI)
      then show "map_option (f ^^ count \<LL> k) (\<Delta>' (Loc k)) = \<Delta>' (Loc k)"
        by (metis count_empty update_locations.simps(2) update_locations_id)
    qed
  qed
qed

lemma var_store_sync_update:
  shows "var_store_sync \<Gamma> f (\<LL> + \<KK>) \<mu> \<longleftrightarrow> var_store_sync (update_locations \<Gamma> f \<LL>) f \<KK> \<mu>"
proof
  show "var_store_sync \<Gamma> f (\<LL> + \<KK>) \<mu> \<Longrightarrow> var_store_sync (update_locations \<Gamma> f \<LL>) f \<KK> \<mu>"
  apply (unfold var_store_sync_def)
  proof(intro allI, safe)
    fix x l \<tau>
    assume "\<mu> x = Some l"
      and "update_locations \<Gamma> f \<LL> (Loc l) = Some \<tau>"
      and "\<forall>x l \<tau>. \<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some ((f ^^ count (\<LL> + \<KK>) l) \<tau>)"
    then obtain \<sigma> where "\<Gamma> (Loc l) = Some \<sigma>"
      by auto
    then have "\<tau> = (f ^^ (count \<LL> l)) \<sigma>"
      using \<open>update_locations \<Gamma> f \<LL> (Loc l) = Some \<tau>\<close> by auto
    then show "update_locations \<Gamma> f \<LL> (V x) = Some ((f ^^ count \<KK> l) \<tau>)"
      by (metis \<open>\<Gamma> (Loc l) = Some \<sigma>\<close> \<open>\<forall>x l \<tau>. \<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some ((f ^^ count (\<LL> + \<KK>) l) \<tau>)\<close> \<open>\<mu> x = Some l\<close> option.simps(9) update_locations.simps(1) update_locations.simps(2) update_locations_union)
  qed

  show "var_store_sync (update_locations \<Gamma> f \<LL>) f \<KK> \<mu> \<Longrightarrow> var_store_sync \<Gamma> f (\<LL> + \<KK>) \<mu>"
    apply (unfold var_store_sync_def)
  proof(intro allI, safe)
    fix x l \<tau>
    assume "\<forall>x l \<tau>. \<mu> x = Some l \<and> update_locations \<Gamma> f \<LL> (Loc l) = Some \<tau> \<longrightarrow> update_locations \<Gamma> f \<LL> (V x) = Some ((f ^^ count \<KK> l) \<tau>)"
      and "\<mu> x = Some l" 
      and "\<Gamma> (Loc l) = Some \<tau>"
    then have "\<Gamma> (V x) = Some ((f ^^ count \<KK> l) ((f ^^ (count \<LL> l)) \<tau>))"
      by (metis option.simps(9) update_locations.simps(1) update_locations.simps(2))
    then show "\<Gamma> (V x) = Some ((f ^^ count (\<LL> + \<KK>) l) \<tau>)"
      by (metis \<open>\<Gamma> (Loc l) = Some \<tau>\<close> option.simps(9) update_locations.simps(2) update_locations_union)
  qed
qed

lemma ty_preserving_it:
  assumes "type_preserving f"
  shows "type_preserving (f^^n)"
  using assms
  apply (auto simp: type_preserving_def)
  apply (induction n)
   apply (simp add: base_type_compat_refl)
  apply auto
  using assms base_type_compat_trans type_preserving_def by blast

lemma ty_preserve_update_loc:
  assumes "type_preserving f" 
    and "\<Gamma> x = Some \<tau>" 
    and "\<tau> \<triangleq> r"
    and "update_locations \<Gamma> f \<LL> x = Some \<sigma>"
  shows "\<sigma> \<triangleq> r"
proof(cases x)
  case (V x1)
  then show ?thesis using assms by auto 
next
  case (Loc x2)
  then show ?thesis using assms
    apply auto
    by (simp add: ty_preserving_it type_preserving_ty_res_compat)
qed

lemma type_preserving_back:
  assumes "type_preserving f"
      and "f \<tau> \<triangleq> r"
    shows "\<tau> \<triangleq> r"
  using assms
  by (metis (no_types, lifting) base_type_compat_trans surjective_pairing ty_res_compat.elims(2) ty_res_compat.simps(1) type_preserving_def)

lemma temp2:
  assumes "update_locations \<Gamma> f \<LL> = \<Delta>"
      and "compat \<Delta> f \<KK> (\<mu>, \<rho>)"
      and "type_preserving f"
    shows "compat \<Gamma> f (\<LL> + \<KK>) (\<mu>, \<rho>)"
  using assms
proof(intro compatI)
  show "\<lbrakk>update_locations \<Gamma> f \<LL> = \<Delta>; compat \<Delta> f \<KK> (\<mu>, \<rho>)\<rbrakk> \<Longrightarrow> var_dom \<Gamma> = dom \<mu>"
    apply (unfold compat_def)
    apply simp
    using update_loc_preserve_dom
    by force

  show "compat \<Delta> f \<KK> (\<mu>, \<rho>) \<Longrightarrow> \<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>"
    by (auto simp: compat_def)

  show "\<lbrakk>update_locations \<Gamma> f \<LL> = \<Delta>; compat \<Delta> f \<KK> (\<mu>, \<rho>)\<rbrakk> \<Longrightarrow> var_store_sync \<Gamma> f (\<LL> + \<KK>) \<mu>"
    by (simp add: compat_elim(3) var_store_sync_update)

  show "compat \<Delta> f \<KK> (\<mu>, \<rho>) \<Longrightarrow> inj \<mu>"
    by (simp add: compat_elim(4))

  show "\<lbrakk>update_locations \<Gamma> f \<LL> = \<Delta>; compat \<Delta> f \<KK> (\<mu>, \<rho>); type_preserving f\<rbrakk> \<Longrightarrow> env_select_compat \<Gamma> (\<mu>, \<rho>)"
    apply (auto simp: env_select_compat_def compat_def)
  proof -
    fix x \<tau>
    assume "type_preserving f" and "\<Delta> = update_locations \<Gamma> f \<LL>"
        and "\<forall>x a b. update_locations \<Gamma> f \<LL> x = Some (a,b) \<longrightarrow> (a,b) \<triangleq> select (\<mu>, \<rho>) x"
        and "\<Gamma> x = Some \<tau>"
    then show "\<tau> \<triangleq> select (\<mu>, \<rho>) x"
    proof(cases x)
      case (V x1)
      then show ?thesis
        by (metis \<open>\<Gamma> x = Some \<tau>\<close> \<open>\<forall>x a b. update_locations \<Gamma> f \<LL> x = Some (a, b) \<longrightarrow> (a, b) \<triangleq> select (\<mu>, \<rho>) x\<close> old.prod.exhaust update_locations.simps(1)) 
    next
      case (Loc x2)
      then have "update_locations \<Gamma> f \<LL> x = Some ((f^^(count \<LL> x2)) \<tau>)"
        using \<open>\<Gamma> x = Some \<tau>\<close> by auto
      then have "((f^^(count \<LL> x2)) \<tau>) \<triangleq> select (\<mu>, \<rho>) x"
        using assms(1) assms(2) compat_elim(5) env_select_compat_def by blast
      then show ?thesis
        using assms(3) ty_preserving_it type_preserving_back by blast 
    qed
  qed

  show "compat \<Delta> f \<KK> (\<mu>, \<rho>) \<Longrightarrow> finite (dom \<rho>)"
    by (auto simp: compat_def)
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
    by (smt option.distinct(1) type_less_general.elims(1))
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
      by (smt domIff option.discI)
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
  (* TODO: This is gross, fix. *)
  proof(rule ext)
    fix x
    show "temp_update_env \<Gamma> (temp_update_env \<Delta> \<Delta>') x = temp_update_env \<Gamma> \<Delta>' x"
      apply (cases x)
       apply simp
      using ConsList sub located_dom_const
      apply (auto simp: map_le_def)
    proof -
    fix a :: nat and b :: SVal and aa :: TyQuant and ba :: BaseTy
      assume a1: "\<And>\<Gamma> m f L a b \<Delta>. \<lbrakk>\<Gamma> \<turnstile>{m} f ; L : (a, b) \<stileturn> \<Delta>; located L\<rbrakk> \<Longrightarrow> dom (\<lambda>l. \<Gamma> (Loc l)) = dom (\<lambda>l. \<Delta> (Loc l))"
      assume a2: "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      assume a3: "located \<L>"
      assume a4: "\<Delta> (Loc (a, b)) = Some (aa, ba)"
      assume a5: "x = Loc (a, b)"
    then obtain pp :: "nat \<times> SVal \<Rightarrow> (nat \<times> SVal \<Rightarrow> (TyQuant \<times> BaseTy) option) \<Rightarrow> TyQuant \<times> BaseTy" where
      "Some (pp (a, b) (\<lambda>p. \<Gamma> (Loc p))) = \<Gamma> x"
      using a4 a3 a2 a1 by (metis (no_types) Resource.distinct(1) domD domI ty_res_compat.elims(2) ty_res_compat.elims(3))
      then show "\<exists>t ba. \<Gamma> (Loc (a, b)) = Some (t, ba)"
        using a5 by (metis (full_types) Resource.distinct(1) ty_res_compat.elims(2) ty_res_compat.elims(3))
    qed
  qed

  then show ?case using head_ty tail_ty loc_type.ConsList by simp
qed

lemma located_locations_in_dom:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "located L"
    shows "set_mset (locations L) \<subseteq> dom (loc_ty_env \<Gamma>)"
  using assms
  apply (induction, auto)
  by (metis domD domI loc_ty_env.simps located_dom_const old.prod.exhaust subset_iff)
  
lemma locator_preservation:
  fixes "\<Sigma>" and "\<L>" and "\<Sigma>'" and "\<L>'"
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> f (locations \<L>) \<Sigma>"
      and "type_preserving f"
      and "\<L> wf"
    shows "(\<exists>\<Gamma>' \<Delta>'. compat \<Gamma>' f (locations \<L>') \<Sigma>'
                \<and> (\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau> \<stileturn> \<Delta>')
                \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' 
                \<and> loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>')"
  using assms
proof(induction arbitrary: \<Gamma> \<tau> f m \<Delta>)
  (* TODO: This is an absurd amount of effort for a relatively easy case... *)
  case (ENat l \<rho> \<mu> n)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (natural, Num n))" by (auto simp: map_le_def) 
  have "\<tau> = (toQuant n, natural)" using ENat loc_type.cases by blast
  let ?\<L>' = "Loc (l, Amount n)"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (natural, Num n))"
  have compat: "compat ?\<Gamma>' f (locations (S ?\<L>')) (\<mu>, ?\<rho>')" using ENat
    using \<open>\<tau> = (toQuant n, natural)\<close> add_fresh_num fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (auto simp: compat_def) 
     apply (unfold var_store_sync_def)
     apply (smt Stored.inject(2) add_mset_eq_single count_empty count_inI domIff fun_upd_apply multi_member_split option.discI)
    
    apply (fold var_store_sync_def)
    apply (auto simp: env_select_compat_def)
    by (metis ENat.prems(2) domI map_le_refl select_preserve)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using ENat.prems using loc_type.cases by blast

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    apply auto
    by (smt ENat.hyps ENat.prems(2) compat_elim(5) domD domI fresh_loc_not_in_env map_le_def)

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' f (locations (S ?\<L>')) (\<mu>, ?\<rho>')"
      and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'"
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
      and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using compat typed var_ty_same loc_ty_sub by auto

  then show ?case using ENat.prems by auto
next
  case (EBool l \<rho> \<mu> b)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (boolean, Bool b))" by (auto simp: map_le_def) 
  have "\<tau> = (any, boolean)" using EBool loc_type.cases by blast
  let ?\<L>' = "Loc (l, SLoc l)"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (boolean, Bool b))"
  have compat: "compat ?\<Gamma>' f (locations (S ?\<L>')) (\<mu>, ?\<rho>')" using EBool
    using \<open>\<tau> = (any, boolean)\<close> add_fresh_loc fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (cases b)
    apply (auto simp: compat_def) 
     apply (unfold var_store_sync_def)
     apply (smt Stored.inject(2) add_mset_eq_single count_empty count_inI domIff fun_upd_apply multi_member_split option.discI)
    
    apply (fold var_store_sync_def)
    apply (auto simp: env_select_compat_def)
    apply (metis EBool.prems(2) domI map_le_refl select_preserve)
     apply (unfold var_store_sync_def)
     apply (smt Stored.inject(2) add_mset_eq_single count_empty count_inI domIff fun_upd_apply multi_member_split option.discI)
    
    apply (fold var_store_sync_def)
    by (metis EBool.prems(2) domI map_le_refl select_preserve)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using EBool.prems using loc_type.cases by blast

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    apply auto
    by (smt EBool.hyps EBool.prems(2) compat_elim(5) domD domI fresh_loc_not_in_env map_le_def)

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' f (locations (S ?\<L>')) (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
      and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using compat typed var_ty_same loc_ty_sub by auto
  then show ?case using EBool.prems by auto
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
    
      then have compat: "compat ?\<Gamma>' f (locations (S ?\<L>')) (\<mu>, \<rho>)" using EVar a1 a2 x_ty final_env
        apply (auto simp: compat_def var_store_sync_def)
         apply (simp add: injD)
        by (smt env_select_compat_def map_upd_Some_unfold type_preserving_ty_res_compat)
    
      have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'"
        by (simp add: Loc final_env a2)
    
      obtain \<Gamma>' and \<Delta>' 
        where "compat \<Gamma>' f (locations (S ?\<L>')) (\<mu>, \<rho>)"
          and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'" 
          and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
          and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
        using compat typed var_ty_same loc_ty_sub by auto

      then show ?thesis using EVar.prems by auto
  next
    case False

    then have compat: "compat ?\<Gamma>' f (locations (S ?\<L>')) (\<mu>, \<rho>)" using EVar x_ty final_env
      apply (auto simp: compat_def var_store_sync_def)
      apply (simp add: injD)
      by (smt EVar.prems(2) compat_elim(1) env_select_compat_def in_type_env_compat map_upd_Some_unfold option.inject select.simps(2) type_preserving_ty_res_compat)

    have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'" using False loc_type.Loc 
      apply (simp add: final_env)
      by (metis fun_upd_same fun_upd_upd)

    obtain \<Gamma>' and \<Delta>' 
      where "compat \<Gamma>' f (locations (S ?\<L>')) (\<mu>, \<rho>)"
        and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'" 
        and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
        and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
      using compat typed var_ty_same loc_ty_sub by auto

    then show ?thesis using EVar.prems by auto
  qed
next
  case (EVarDef x \<mu> l \<rho> t)
  then have final_env: "\<Delta> = \<Gamma>(V x \<mapsto> f (empty,t))" by simp (erule loc_type.cases, auto)

  let ?\<Gamma>' = "\<Delta>(Loc (l, SLoc l) \<mapsto> (empty,t))"
  let ?\<Delta>' = "?\<Gamma>'(Loc (l, SLoc l) \<mapsto> f (empty,t))"
  let ?\<mu>' = "\<mu>(x \<mapsto> (l, SLoc l))"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (t, emptyVal t))"
  let ?\<L>' = "Loc (l, SLoc l)"

  have compat: "compat ?\<Gamma>' f (locations (S ?\<L>')) (?\<mu>', ?\<rho>')" 
  proof(rule compatI)
    show "var_dom (\<Delta>(Loc (l, SLoc l) \<mapsto> (TyQuant.empty, t))) = dom (\<mu>(x \<mapsto> (l, SLoc l)))"
      using final_env EVarDef by (auto simp: compat_def)

    show "\<forall>k. k \<notin> dom (\<rho>(l \<mapsto> Res (t, emptyVal t))) \<longrightarrow> k \<notin> references (\<mu>(x \<mapsto> (l, SLoc l)))"
      using EVarDef by (auto simp: compat_def)

    show "var_store_sync (\<Delta>(Loc (l, SLoc l) \<mapsto> (TyQuant.empty, t))) f (locations (S (Loc (l, SLoc l)))) (\<mu>(x \<mapsto> (l, SLoc l)))"
      using EVarDef.prems(4) wf_locator.cases by blast

    show "inj (\<mu>(x \<mapsto> (l, SLoc l)))"
      using EVarDef
      apply auto
      by (smt EVarDef.hyps(2) Resource.distinct(1) compat_elim(1) compat_elim(4) compat_elim(5) fun_upd_apply in_var_env_select inj_on_def not_err_in_dom)

    show "env_select_compat (\<Delta>(Loc (l, SLoc l) \<mapsto> (TyQuant.empty, t))) (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t)))"
      using final_env EVarDef
      apply (auto simp: env_select_compat_def)
      apply (metis base_type_compat_refl ty_res_compat.simps(1) type_preserving_ty_res_compat)
       apply (simp add: base_type_compat_refl)
      by (smt EVarDef.hyps(1) compat_elim(2) compat_elim(5) domIff env_select_compat_def fun_upd_triv map_le_imp_upd_le option.discI select_preserve2 upd_None_map_le)

    show "finite (dom (\<rho>(l \<mapsto> Res (t, emptyVal t))))"
      using EVarDef by (auto simp: compat_def)
  qed

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : (empty,t) \<stileturn> ?\<Delta>'"
    by (meson Loc fun_upd_same)

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    apply auto
    using EVarDef.prems(4) wf_locator.simps by blast

  have "\<tau> = (empty,t)" using EVarDef loc_type.cases by blast

  then obtain \<Gamma>' and \<Delta>'
      where "compat \<Gamma>' f (locations (S ?\<L>')) (\<mu>, \<rho>)"
        and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'"
        and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
        and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using compat typed var_ty_same loc_ty_sub
    using EVarDef.prems(4) wf_locator.simps by blast 

  then show ?case
    using \<open>\<tau> = (TyQuant.empty, t)\<close> compat loc_ty_sub typed var_ty_same by blast
next               
  case (EConsListHeadCongr \<Sigma> \<L> \<Sigma>' \<L>' \<tau>' Tail \<Gamma> \<tau>)

  have "\<L> wf" using EConsListHeadCongr wf_locator.cases
    by blast

  obtain \<Delta>'' and q
    where "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''" and tail_ty: "\<Delta>'' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Delta>"
      and "\<tau> = (one \<oplus> q, table [] \<tau>')"
    using EConsListHeadCongr 
    apply auto 
    apply (erule loc_type.cases)
    by blast+

  have "locations Tail = {#}" and "Tail wf" using EConsListHeadCongr
    using head_step_wf(1) apply blast
    using EConsListHeadCongr head_step_wf(2) by blast

  then obtain \<Gamma>' and \<Delta>' 
    where "compat \<Gamma>' f (locations \<L>') \<Sigma>'" 
      and "\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'" 
      and var_env_eq: "var_ty_env \<Delta>'' = var_ty_env \<Delta>'"
      and loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using EConsListHeadCongr \<open>\<L> wf\<close>
    by (metis \<open>\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''\<close> add_cancel_left_right locations.simps(7))

  then obtain \<Xi>' 
    where "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Xi>'" 
      and "var_ty_env \<Delta> = var_ty_env \<Xi>'"
      and "loc_ty_env \<Xi>' = loc_ty_env \<Delta>'"
    using EConsListHeadCongr tail_ty prf_compat_not_located var_env_eq
    by (meson \<open>Tail wf\<close> \<open>locations Tail = {#}\<close>) 

  then show ?case using EConsListHeadCongr \<open>locations Tail = {#}\<close> \<open> compat \<Gamma>' f (locations \<L>') \<Sigma>' \<close>
  proof(intro exI conjI)
    show "compat \<Gamma>' f (locations [ \<tau>' ; \<L>' , Tail ]) \<Sigma>'"
      by (simp add: \<open>Psamathe.compat \<Gamma>' f (locations \<L>') \<Sigma>'\<close> \<open>locations Tail = {#}\<close>)
    show "var_ty_env \<Delta> = var_ty_env \<Xi>'"
      using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>'\<close> by auto
    show "\<Gamma>' \<turnstile>{s} f ; [ \<tau>' ; \<L>' , Tail ] : \<tau> \<stileturn> \<Xi>'" using \<open>\<tau> = (one \<oplus> q, table [] \<tau>')\<close>
      apply simp
    proof(rule loc_type.ConsList)
      show "\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'"
        by (simp add: \<open>\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau>' \<stileturn> \<Delta>'\<close>)
      show "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Xi>'"
        by (simp add: \<open>\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Xi>'\<close>)
    qed
    show "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'" using loc_ty_sub by simp
  qed
next
  case (EConsListTailCongr \<L> \<Sigma> Tail \<Sigma>' Tail' \<tau>')

  obtain \<Delta>'' and q
    where head_ty: "\<Gamma> \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>''" 
      and tail_ty: "\<Delta>'' \<turnstile>{s} f ; Tail : (q, table [] \<tau>') \<stileturn> \<Delta>"
      and "\<tau> = (one \<oplus> q, table [] \<tau>')"
    using EConsListTailCongr 
    apply auto 
    apply (erule loc_type.cases)
    by blast+

  obtain \<mu> \<rho> where "\<Sigma> = (\<mu>, \<rho>)" by (cases \<Sigma>)

  have "\<L> wf" and "Tail wf" using EConsListTailCongr wf_locator.cases
    by blast+
  then have "compat \<Delta>'' f (locations Tail) (\<mu>,\<rho>)" 
        and a2: "update_locations \<Gamma> f (locations \<L>) = \<Delta>''"
    using EConsListTailCongr \<open> located \<L> \<close> head_ty
    apply simp
    apply (rule located_env_compat2)
    apply auto
    using \<open>\<Sigma> = (\<mu>, \<rho>)\<close>
    apply blast
    using EConsListTailCongr.hyps(1) EConsListTailCongr.prems(2) EConsListTailCongr.prems(3) \<open>\<Sigma> = (\<mu>, \<rho>)\<close> head_ty located_env_compat by auto

  then obtain \<Delta>' \<Xi> 
    where temp_compat: "compat \<Delta>' f (locations Tail') \<Sigma>'"
      and "\<Delta>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Xi>" 
      and "var_ty_env \<Delta> = var_ty_env \<Xi>"
      and "loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
    using EConsListTailCongr tail_ty \<open> Tail wf \<close> \<open>\<Sigma> = (\<mu>, \<rho>)\<close> by blast

  let ?\<Gamma>' = "temp_update_env \<Gamma> \<Delta>'"
  have "?\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>'"
    using EConsListTailCongr.hyps(1) \<open>loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'\<close> head_ty located_var_ignore by auto

  have "set_mset (locations \<L>) \<subseteq> dom (loc_ty_env \<Gamma>)"
    using EConsListTailCongr.hyps(1) head_ty located_locations_in_dom by auto

  then have "update_locations ?\<Gamma>' f (locations \<L>) = \<Delta>'" using a2
    using \<open>loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'\<close> temp1 by auto

  then show ?case
  proof(intro exI conjI)
    (* TODO: Cleanup *)

    show "Psamathe.compat ?\<Gamma>' f (locations [ \<tau>' ; \<L> , Tail' ]) \<Sigma>'"
      apply simp
      by (metis (no_types, lifting) EConsListTailCongr.prems(3) Psamathe.compat_def \<open>update_locations (temp_update_env \<Gamma> \<Delta>') f (locations \<L>) = \<Delta>'\<close> case_prodE temp2 temp_compat)

    show "var_ty_env \<Delta> = var_ty_env \<Xi>" using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>\<close> by simp

    show "?\<Gamma>' \<turnstile>{s} f ; [ \<tau>' ; \<L> , Tail' ] : \<tau> \<stileturn> \<Xi>"
      using ConsList \<open>\<Delta>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Xi>\<close> \<open>\<tau> = (one \<oplus> q, table [] \<tau>')\<close> \<open>(temp_update_env \<Gamma> \<Delta>') \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>'\<close> by auto

    show "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
      by (auto simp: map_le_def)
  qed
qed

end
