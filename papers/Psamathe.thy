theory Psamathe
  imports Main "HOL-Library.Multiset"
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

datatype Val = Num nat | Bool bool 
  | Table "nat list"
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

(* Auxiliary definitions *)

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

fun selectLoc :: "(nat, Resource) map \<Rightarrow> StorageLoc \<Rightarrow> Resource" where
  "selectLoc \<rho> (l, Amount n) = (case \<rho> l of Some (Res (t,_)) \<Rightarrow> Res (t, Num n) | _ \<Rightarrow> error)"
| "selectLoc \<rho> (l, SLoc k) = 
    (if l = k then 
      (case \<rho> l of None \<Rightarrow> error | Some r \<Rightarrow> r)
     else 
      (case \<rho> l of 
        Some (Res (t, Table vals)) \<Rightarrow> if k \<in> set vals then Res (t, Table [k]) else error
       | None \<Rightarrow> error 
      )
    )"

fun select :: "Store \<Rightarrow> Stored \<Rightarrow> Resource" where
  "select (\<mu>, \<rho>) (V x) = (case \<mu> x of Some l \<Rightarrow> selectLoc \<rho> l | None \<Rightarrow> error)"
| "select (\<mu>, \<rho>) (Loc l) = selectLoc \<rho> l"

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

(* TODO: Not clear this is needed, as the select property of compat should be sufficient, I think *)
fun loc_dom :: "Env \<Rightarrow> nat set" where
  "loc_dom \<Gamma> = { l . \<exists>a. Loc (l, a) \<in> dom \<Gamma> }"

fun type_less_general :: "Type option \<Rightarrow> Type option \<Rightarrow> bool" (infix "\<preceq>\<^sub>\<tau>" 50) where
  "type_less_general (Some (q,t)) (Some (r,u)) = (q \<sqsubseteq> r \<and> t = u)"
| "type_less_general None None = True"
| "type_less_general _ _ = False"

fun references :: "(string, StorageLoc) map \<Rightarrow> nat set" where
  "references \<mu> = { l . \<exists>x k j. \<mu> x = Some (k, j) \<and> (k = l \<or> j = SLoc l) }"

fun finite_store :: "Store \<Rightarrow> bool" where
  "finite_store (\<mu>, \<rho>) = (finite (dom \<mu>) \<and> finite (dom \<rho>))"

fun locations :: "Locator \<Rightarrow> StorageLoc multiset" where
  "locations (N n) = {#}"
| "locations (B b) = {#}"
| "locations (S (V x)) = {#}"
| "locations (S (Loc l)) = {#l#}"
| "locations (var x : t) = {#}"
| "locations [ \<tau> ; ] = {#}"
| "locations [ \<tau> ; \<L>, Tail ] = (locations \<L> + locations Tail)"

inductive wf_locator :: "Locator \<Rightarrow> bool" ("_ wf" 10) where
  EmptyWf: "[ \<tau> ; ] wf"
| VarWf: "S x wf"
| NatWf: "N n wf"
| BoolWf: "B b wf"
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

definition var_store_sync :: "Env \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> bool" where
  "var_store_sync \<Gamma> f \<LL> \<mu> \<equiv> 
    \<forall>x l \<tau>. (\<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau>) \<longrightarrow> \<Gamma> (V x) = Some ((f^^(count \<LL> l)) \<tau>)"

definition env_select_compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" where
  "env_select_compat \<Gamma> \<Sigma> \<equiv> \<forall>x \<tau>. \<Gamma> x = Some \<tau> \<longrightarrow> ty_res_compat \<tau> (select \<Sigma> x)"

(* NOTE: compat can take a function from Vars/Locs to updaters (default to id) instead of a single function,
          this may let us get rid of some of the issues we face due to the updater changing throughout 
          the rules ... *)
definition compat :: "Env \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> Store \<Rightarrow> bool" where
  "compat \<Gamma> f \<LL> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> 
                        var_dom \<Gamma> = dom \<mu> \<and>
                        (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>) \<and>
                        var_store_sync \<Gamma> f \<LL> \<mu> \<and>
                        inj \<mu> \<and> finite (dom \<rho>) \<and>
                        env_select_compat \<Gamma> (\<mu>, \<rho>)"
                        (*(\<forall>x. exact_type (select (\<mu>, \<rho>) x) \<preceq>\<^sub>\<tau> \<Gamma> x))" *)

lemma compat_elim[elim]:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
  shows "var_dom \<Gamma> = dom \<mu>" 
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>" 
    and "var_store_sync \<Gamma> f \<LL> \<mu>"
    and "inj \<mu>" 
    and "env_select_compat \<Gamma> (\<mu>, \<rho>)"
  using assms
  by (auto simp: compat_def)

lemma in_type_env_select:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)"
      and "x \<in> dom \<Gamma>"
  obtains r where "select (\<mu>, \<rho>) x = Res r"
  using assms
  by (metis Resource.exhaust domD env_select_compat_def ty_res_compat.simps(2))

lemma select_loc_update:
  fixes \<rho> \<rho>' l k
  assumes "selectLoc \<rho> (l,k) \<noteq> error"
      and "\<rho> \<subseteq>\<^sub>m \<rho>'"
    shows "selectLoc \<rho>' (l,k) \<noteq> error"
  using assms
proof(cases k)
  case (SLoc x1)
  then show ?thesis using assms SLoc
      apply (cases "\<rho> l")
      apply (auto simp: map_le_def)
      by force+
next
  case (Amount x2)
  then obtain temp where "\<rho> l = Some temp" using assms by fastforce
  then obtain r where "\<rho> l = Some (Res r)" using assms Amount
    apply auto
    by (metis Resource.simps(5) exact_type.cases) (* TODO: why is it using exact_type? *)
  then have "\<rho>' l = Some (Res r)" using assms map_le_def domI
    by metis
  then show ?thesis using Amount assms by (simp add: \<open>\<rho> l = Some (Res r)\<close>)
qed

lemma select_update:
  fixes \<mu> \<rho> \<mu>' \<rho>' x
  assumes "select (\<mu>, \<rho>) x \<noteq> error"
      and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'"
    shows "select (\<mu>', \<rho>') x \<noteq> error"
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
    by (metis \<open>\<mu> x1 = Some l\<close> option.simps(5) select_loc_update surj_pair)
next
  case (Loc x2)
  then show ?thesis
    apply auto
    by (metis assms(1) assms(3) select.simps(2) select_loc_update surj_pair)
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
  shows "selectLoc \<rho>' l \<noteq> error"
  using assms 
  apply auto 
  by (metis select_loc_update surj_pair)

lemma type_preserving_works:
  fixes f q t r s
  assumes "type_preserving f" and "t \<approx> s"
  obtains q' t' where "f (q,t) = (q', t')" and "t' \<approx> s"
  using assms
  apply (auto simp: type_preserving_def)
  using base_type_compat_sym base_type_compat_trans prod.exhaust_sel by blast

lemma select_loc_preserve_var:
  fixes \<Gamma> \<mu> \<rho> \<rho>' x l k
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" 
    and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "V x \<in> dom \<Gamma>" and "\<mu> x = Some (l,k)"
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>"
  shows "selectLoc \<rho> (l,k) = selectLoc \<rho>' (l,k)"
  using assms
  apply (cases k, auto simp: map_le_def env_select_compat_def)
  by metis+

lemma compat_loc_in_env:
  fixes \<Gamma> \<mu> \<rho> l k
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "Loc (l,k) \<in> dom \<Gamma>"
  obtains r where "selectLoc \<rho> (l,k) = Res r"
  using assms
  by (metis in_type_env_select select.simps(2))

lemma select_loc_preserve_loc:
  fixes \<Gamma> \<mu> \<rho> \<rho>' l k
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "Loc (l,k) \<in> dom \<Gamma>"
  shows "selectLoc \<rho> (l,k) = selectLoc \<rho>' (l,k)"
  using assms
  apply (cases k, auto simp: map_le_def env_select_compat_def)
  apply (metis domIff option.simps(4) select.simps(2) selectLoc.simps(2) ty_res_compat.simps(2))
  apply (cases "\<rho> l")
  apply auto
  apply fastforce
  apply (metis (no_types, lifting) domI option.simps(5))
  by (metis (no_types, lifting) Resource.distinct(1) assms(1) assms(3) compat_loc_in_env domIff option.simps(4) selectLoc.simps(1))

lemma select_preserve:
  fixes \<Gamma> \<mu> \<rho> \<mu>' \<rho>' x
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "x \<in> dom \<Gamma>"
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
  then obtain l and k where "x2 = (l, k)" by (cases x2)
  then show ?thesis using assms Loc
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
  then obtain l and k where "x2 = (l, k)" by (cases x2)
  then show ?thesis using assms Loc
    apply (simp only: select.simps)
    using compat_elim(5) select_loc_preserve_loc by blast
qed

lemma not_err_in_dom:
  fixes \<rho> l k
  assumes "selectLoc \<rho> (l,k) \<noteq> error"
  shows "l \<in> dom \<rho>"
  using assms
proof(cases k)
  case (SLoc x1)
  then show ?thesis using assms 
    by (cases "\<rho> l", cases "l = x1", auto)
next
  case (Amount x2)
  then show ?thesis using assms by (cases "\<rho> l", auto)
qed

lemma fresh_loc_not_in_env:
  fixes \<Gamma> \<mu> \<rho> l k j
  assumes "env_select_compat \<Gamma> (\<mu>, \<rho>)" and "l \<notin> dom \<rho>"
  shows "Loc (l, k) \<notin> dom \<Gamma>"
  using assms compat_loc_in_env not_err_in_dom
  apply auto
  by (metis Resource.distinct(1) assms(2) domI)

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

definition sublocator :: "Locator \<Rightarrow> Locator \<Rightarrow> bool" (infix "\<subseteq>\<^sub>L" 50) where
  "\<L> \<subseteq>\<^sub>L \<K> \<equiv> \<L> = \<K> 
           \<or> (case \<K> of
                [ \<tau> ; \<L>', Tail ] \<Rightarrow> \<L> = \<L>' \<or> \<L> = Tail
              | _ \<Rightarrow> False)"

lemma sublocator_resp_locations:
  assumes "\<L> \<subseteq>\<^sub>L \<K>" 
  shows "locations \<L> \<subseteq># locations \<K>"
  using assms
  apply (unfold sublocator_def)
  apply (cases \<L>)
  by (cases \<K>, auto)+

(*
lemma var_store_sync_resp_locations:
  assumes "locations \<L> \<subseteq> locations \<K>" 
      and "var_store_sync \<Gamma> (locations \<K>) \<mu>"
  shows "var_store_sync \<Gamma> (locations \<L>) \<mu>"
proof(unfold var_store_sync_def, intro allI, safe)
  fix x \<tau> l
  assume "\<mu> x = Some l" and "\<Gamma> (Loc l) = Some \<tau>" and "l \<notin> locations \<L>"
  then have "l \<notin> locations \<K>" using assms
  show "\<Gamma> (V x) = Some \<tau>"

lemma compat_resp_locations:
  assumes "locations \<L> \<subseteq> locations \<K>" and "\<Gamma> \<leftrightarrow>\<^sup>\<K> \<Sigma>"
  shows "\<Gamma> \<leftrightarrow>\<^sup>\<L> \<Sigma>"

lemma sublocator_inherit_compat:
  assumes "\<Gamma> \<leftrightarrow>\<^sup>\<L> \<Sigma>" and "\<K> \<subseteq>\<^sub>L \<L>"
  shows "\<Gamma> \<leftrightarrow>\<^sup>\<K> \<Sigma>" *)

lemma compat_transfer_var_sync:
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" 
      and "var_store_sync \<Gamma> f \<LL>' \<mu>"
    shows "compat \<Gamma> f \<LL>' (\<mu>, \<rho>)"
  using assms
  by (auto simp: compat_def var_store_sync_def)

lemma diff_in_loc_var_ty_env_same:
  assumes "\<forall>x. \<Gamma> x \<noteq> \<Gamma>' x \<longrightarrow> (\<exists>l. x = Loc l)"
  shows "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
  using assms
  by auto

(*
lemma compat_apply_f:
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
      and "\<forall>x. \<Gamma> x \<noteq> \<Gamma>' x \<longrightarrow> (\<exists>l. x = Loc l \<and> l \<in> \<LL> \<and> map_option f (\<Gamma> (Loc l)) = \<Gamma>' (Loc l))"
    shows "compat \<Gamma>' f \<LL> (\<mu>, \<rho>)"
  using assms diff_in_loc_var_ty_env_same
  apply (auto simp: compat_def var_store_sync_def)
  apply (smt domD domI mem_Collect_eq old.prod.exhaust)
  apply (smt assms(1) domD domI in_type_env_compat mem_Collect_eq ty_res_compat.elims(2))
  apply (metis (no_types, lifting) Stored.inject(2)) *)

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
  assumes "var_store_sync \<Gamma> f \<LL> \<mu>"
      and "\<mu> x = Some l"
      and "\<Gamma> (Loc l) = Some \<tau>"
    shows "\<Gamma> (V x) = Some ((f^^(count \<LL> l)) \<tau>)"
  using assms var_store_sync_def
  by blast

lemma var_store_sync_add:
  assumes "var_store_sync \<Gamma> f ({#l#} + \<LL>) \<mu>"
      and "\<Gamma> (Loc l) = Some \<tau>"
      and "\<mu> x = Some l"
  shows "var_store_sync (\<Gamma>(Loc l \<mapsto> f \<tau>)) f \<LL> \<mu>"
  using assms
proof -
  have "\<Gamma> (V x) = map_option (f^^(count ({#l#} + \<LL>) l)) (\<Gamma> (Loc l))" using assms
    by (simp add: var_store_sync_use)
  then show ?thesis using assms
    apply (auto simp: var_store_sync_def)
    by (metis funpow_swap1 old.prod.exhaust)
qed

lemma var_store_sync_no_var:
  assumes "var_store_sync \<Gamma> f ({#l#} + \<LL>) \<mu>"
    and "\<not>(\<exists>x. \<mu> x = Some l)"
  shows "var_store_sync (\<Gamma>(Loc l \<mapsto> \<tau>)) f \<LL> \<mu>" 
  using assms
  by (auto simp: var_store_sync_def)

fun update_locations :: "Env \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> Env" where
  "update_locations \<Gamma> f \<LL> (V x) = \<Gamma> (V x)"
| "update_locations \<Gamma> f \<LL> (Loc l) = map_option (f^^(count \<LL> l)) (\<Gamma> (Loc l))"

lemma update_locations_id: "update_locations \<Gamma> f {#} = \<Gamma>"
  sorry

lemma update_locations_union: 
  assumes "update_locations \<Gamma> f \<LL> = \<Delta>"
      and "update_locations \<Delta> f \<KK> = \<Xi>"
    shows "update_locations \<Gamma> f (\<LL> + \<KK>) = \<Xi>"
  sorry

lemma update_locations_step: "(\<lambda>a. if a = Loc l then Some (f \<tau>) else \<Gamma> a) = update_locations \<Gamma> f {#l#}"
  sorry

lemma located_env_compat:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> f (locations \<L> + \<LL>) (\<mu>, \<rho>)"
      and "located \<L>"
      and "type_preserving f"
    shows "compat \<Delta> f \<LL> (\<mu>, \<rho>) \<and> \<Delta> = update_locations \<Gamma> f (locations \<L>)"
  using assms
proof(induction arbitrary: \<mu> \<rho> \<LL> rule: loc_type.induct)
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
      apply (simp add: var_store_sync_add)
      apply (smt env_select_compat_def fun_upd_apply option.inject type_preserving_ty_res_compat)
      by (simp add: update_locations_step)
  next
    case False
    then show ?thesis using Loc
      apply (unfold compat_def, clarsimp, safe)
      apply (simp add: var_store_sync_no_var)
      apply (smt env_select_compat_def fun_upd_apply option.inject type_preserving_ty_res_compat)
      by (simp add: update_locations_step)
  qed 
next
  case (VarDef x \<Gamma> f t)
  then show ?case by simp 
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case
    by (simp add: update_locations_id)
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have "located \<L>" and "located Tail" 
        and "Psamathe.compat \<Gamma> f (locations \<L> + locations Tail + \<LL>) (\<mu>, \<rho>)"
        and "\<Delta> = update_locations \<Gamma> f (locations \<L>)"
        apply simp
    using ConsList.prems(2) apply auto[1]
    using ConsList.prems(1) apply auto[1]
    by (metis ConsList.IH(1) ConsList.prems(1) ConsList.prems(2) ConsList.prems(3) add.assoc located.simps(3) locations.simps(7))
  then have "Psamathe.compat \<Delta> f (locations Tail + \<LL>) (\<mu>, \<rho>)" using ConsList
    apply auto
    by (metis ab_semigroup_add_class.add_ac(1))
  then show "Psamathe.compat \<Xi> f \<LL> (\<mu>, \<rho>) \<and> \<Xi> = update_locations \<Gamma> f (locations [\<tau>; \<L>, Tail])" 
    using ConsList
    apply auto
    apply blast
    by (simp add: \<open>\<Delta> = update_locations \<Gamma> f (locations \<L>)\<close> update_locations_union)
qed

(* TODO: Clean up this and the other version *)
lemma located_env_compat2:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> f (locations \<L> + \<LL>) (\<mu>, \<rho>)"
      and "located \<L>"
      and "type_preserving f"
    shows "compat \<Delta> f \<LL> (\<mu>, \<rho>)" and "\<Delta> = update_locations \<Gamma> f (locations \<L>)"
  using assms
  using located_env_compat apply auto[1]
  using assms(1) assms(2) assms(3) assms(4) located_env_compat by auto

lemma locator_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> f (locations \<L> + \<LL>) (\<mu>, \<rho>)"
      and "\<L> wf"
      and "finite (dom \<rho>)"
      and "type_preserving f"
  shows "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. <(\<mu>, \<rho>), \<L>> \<rightarrow> <(\<mu>', \<rho>'), \<L>'> )"
  using assms
proof(induction arbitrary: \<mu> \<rho> m \<LL> rule: loc_type.induct)
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
  then have env_compat: "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" by simp
  have not_in_lookup: "x \<notin> dom \<mu>" using VarDef by (auto simp: compat_def)
  have "finite (dom \<rho>)" using VarDef by simp
  then obtain l where has_loc: "l \<notin> dom \<rho>" using gen_loc env_compat not_in_lookup by blast
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
  then have env_compat: "compat \<Gamma> f (locations \<L> + locations Tail + \<LL>) (\<mu>, \<rho>)" by auto

  from ConsList and wf_locator.cases 
  have "\<L> wf" and "Tail wf" and "finite (dom \<rho>)" and "type_preserving f" by fastforce+

  from this and env_compat 
  have loc_induct: "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. < (\<mu>, \<rho>) , \<L> > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >)"
  and tail_induct: "\<And>\<mu>' \<rho>'. \<lbrakk>compat \<Delta> f (locations Tail + \<LL>) (\<mu>, \<rho>)\<rbrakk>
                         \<Longrightarrow> located Tail \<or> (\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >)"
    by (simp_all add: ConsList union_assoc)
   
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
      from loc_l have "compat \<Delta> f (locations Tail + \<LL>) (\<mu>, \<rho>)" 
        using located_env_compat ConsList env_compat
        by (metis ab_semigroup_add_class.add_ac(1)) 
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

lemma add_fresh_num:
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
      and "set_mset \<LL> \<subseteq> { l . Loc l \<in> dom \<Gamma> }"
      and "Loc (l, Amount n) \<notin> dom \<Gamma>"
      and "l \<notin> dom \<rho>"
      and "exact_type (Res (t, Num n)) = Some \<tau>"
    shows "compat (\<Gamma>(Loc (l, Amount n) \<mapsto> \<tau>)) f \<LL> (\<mu>, \<rho>(l \<mapsto> Res (t, Num n)))"
  using assms
  apply (auto simp: compat_def var_store_sync_def env_select_compat_def)
  apply blast
  apply (simp add: base_type_compat_refl)
  by (metis (mono_tags, lifting) assms(1) domI fun_upd_triv map_le_imp_upd_le map_le_refl select_preserve)

lemma exact_type_preserves_tyquant:
  shows "\<exists>q. exact_type (Res (t, v)) = Some (q, t)"
  by (cases v, auto)

lemma add_fresh_loc:
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
      and "set_mset \<LL> \<subseteq> { l . Loc l \<in> dom \<Gamma> }"
      and "Loc (l, SLoc l) \<notin> dom \<Gamma>"
      and "l \<notin> dom \<rho>"
      and "exact_type (Res (t, v)) = Some \<tau>"
      and "\<tau> \<sqsubseteq>\<^sub>\<tau> \<sigma>"
    shows "compat (\<Gamma>(Loc (l, SLoc l) \<mapsto> \<sigma>)) f \<LL> (\<mu>, \<rho>(l \<mapsto> Res (t, v)))"
  using assms
  apply (auto simp: compat_def var_store_sync_def env_select_compat_def)
  apply blast
  apply (metis base_type_compat_refl exact_type_preserves_tyquant less_general_type.simps option.inject)
  by (smt assms(1) domIff fun_upd_triv map_le_imp_upd_le map_le_refl option.discI select_preserve)

definition var_loc_compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" where
  "var_loc_compat \<Gamma> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> 
      \<forall>x l. \<mu> x = Some l \<and> Loc l \<in> dom \<Gamma> \<and> V x \<in> dom \<Gamma> \<longrightarrow> \<Gamma> (Loc l) = \<Gamma> (V x)"

definition prf_compat_simple :: "Env \<Rightarrow> Store \<Rightarrow> Env \<Rightarrow> bool" ("_ \<lhd>\<^sup>_ _" 50) where
  "prf_compat_simple \<Gamma> \<Sigma> \<Gamma>' \<equiv> var_ty_env \<Gamma> = var_ty_env \<Gamma>' \<and> var_loc_compat \<Gamma>' \<Sigma>"

lemma prf_compat_simpleI[intro]:
  assumes "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
      and "var_loc_compat \<Gamma>' \<Sigma>"
    shows "prf_compat_simple \<Gamma> \<Sigma> \<Gamma>'"
  using assms
  by (auto simp: prf_compat_simple_def)

(*
lemma prf_compat_upd:
  fixes \<Gamma> \<Gamma>' x \<tau>
  assumes "\<Gamma> \<lhd>\<^sup>\<mu> \<Gamma>'"
    shows "\<Gamma>(V x \<mapsto> \<tau>) \<lhd>\<^sup>\<mu> \<Gamma>'(V x \<mapsto> \<tau>)"
  using assms
  apply (auto simp: prf_compat_simple_def)
  apply meson *)

(*
lemma prf_compat_not_located:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
      and "L wf"
      and "\<forall>l \<in> set_mset (locations L). \<Gamma> (Loc l) = \<Gamma>' (Loc l)"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>') 
                \<and> var_ty_env \<Delta> = var_ty_env \<Delta>' 
                \<and> (\<forall>l \<in> set_mset (locations L). \<Delta> (Loc l) = \<Delta>' (Loc l))"
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
    by (metis (no_types, hide_lams) Stored.inject(1) fun_upd_apply loc_type.Var)
next
  case (Loc \<Gamma> l \<tau> m f)
  then show ?case 
    apply auto
    by (metis Stored.distinct(1) fun_upd_apply loc_type.Loc)
next
  case (VarDef x \<Gamma> f t)
  then show ?case using loc_type.VarDef
    apply simp
    by (metis (mono_tags, hide_lams) Stored.inject(1) domD domI fun_upd_apply)
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
  then obtain \<Delta>' 
    where "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" 
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'" 
      and "\<forall>l \<in> set_mset (locations L). \<Delta> (Loc l) = \<Delta>' (Loc l)"
    using ConsList
    apply auto
  then obtain \<Xi>' where "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'"  and "var_ty_env \<Xi> = var_ty_env \<Xi>'"
    using ConsList \<open> Tail wf \<close>
    apply auto
  then show ?case
    apply auto
  qed
*)

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

inductive loc_eval_bigstep :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> Locator \<Rightarrow> bool"
  ("< _ , _ > \<Down> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<Down> < (\<mu>, \<rho>(l \<mapsto> Res (natural, Num n))), S (Loc (l, Amount n)) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<Down> < (\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b))), S (Loc (l, SLoc l)) >"
| EVar: "\<lbrakk> \<mu> x = Some l \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), S (V x) > \<Down> < (\<mu>, \<rho>), S (Loc l) >"
| ELoc: "< (\<mu>, \<rho>), S (Loc l) > \<Down> < (\<mu>, \<rho>), S (Loc l) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<Down> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t))), S (Loc (l, SLoc l)) >"
| EEmptyList: "< \<Sigma>, [ \<tau> ; ] > \<Down> < \<Sigma>, [ \<tau> ; ] >"
| EConsList: "\<lbrakk> < \<Sigma>, \<L> > \<Down> < \<Sigma>', \<L>' >; <\<Sigma>', Tail> \<Down> <\<Sigma>'', Tail'> \<rbrakk>
                   \<Longrightarrow> < \<Sigma>, [ \<tau> ; \<L>, Tail ] > \<Down> < \<Sigma>'', [ \<tau> ; \<L>', Tail' ] >"

definition test :: "Env \<Rightarrow> Store \<Rightarrow> bool" where
  "test \<Gamma> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow>
                    var_dom \<Gamma> = dom \<mu> \<and>
                    (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>) \<and>
                    inj \<mu> \<and> finite (dom \<rho>) \<and>
                    env_select_compat \<Gamma> (\<mu>, \<rho>)"

lemma testI[intro]:
  assumes "var_dom \<Gamma> = dom \<mu>" 
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>"
    and "inj \<mu>" 
    and "finite (dom \<rho>)"
    and "env_select_compat \<Gamma> (\<mu>, \<rho>)"
  shows "test \<Gamma> (\<mu>, \<rho>)"
  using assms
  by (auto simp: test_def)

lemma test_elim[elim]:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "test \<Gamma> (\<mu>, \<rho>)"
  shows "var_dom \<Gamma> = dom \<mu>" 
    and "\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>"
    and "inj \<mu>" 
    and "finite (dom \<rho>)"
    and "env_select_compat \<Gamma> (\<mu>, \<rho>)"
  using assms
  by (auto simp: test_def)

lemma select_preserve_test:
  fixes \<Gamma> \<mu> \<rho> \<mu>' \<rho>' x
  assumes "test \<Gamma> (\<mu>, \<rho>)" and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "x \<in> dom \<Gamma>"
  shows "select (\<mu>, \<rho>) x = select (\<mu>', \<rho>') x"
  using assms
proof(cases x)
  case (V x1)
  then have "x1 \<in> dom \<mu>" using assms by (auto simp: test_def)
  then have "\<mu> x1 = \<mu>' x1" using assms by (simp add: map_le_def)
  then show ?thesis using assms V \<open>x1 \<in> dom \<mu>\<close>
    apply auto
    by (metis assms(4) option.simps(5) select_loc_preserve_var test_elim(2) test_elim(5))
next
  case (Loc x2)
  then obtain l and k where "x2 = (l, k)" by (cases x2)
  then show ?thesis using assms Loc
    apply (simp only: select.simps)
    using select_loc_preserve_loc test_elim(5) by blast
qed

lemma locator_bigstep_works:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "test \<Gamma> (\<mu>, \<rho>)"
      and "type_preserving f"
    shows "\<exists>\<mu>' \<rho>' L'. <(\<mu>, \<rho>), L> \<Down> <(\<mu>', \<rho>'), L'> \<and> located L' \<and> test \<Delta> (\<mu>', \<rho>')"
  using assms
proof(induction arbitrary: \<mu> \<rho> rule: loc_type.induct)
  case (Nat \<Gamma> f n)
  then obtain "l" where "l \<notin> dom \<rho>" using gen_loc
    using test_elim(4) by blast 
  show ?case
  proof(intro exI conjI)
    show "<(\<mu>, \<rho>), N n> \<Down> <(\<mu>, \<rho>(l \<mapsto> Res (natural, Num n))), S (Loc (l, Amount n))>"
      by (simp add: \<open>l \<notin> dom \<rho>\<close> loc_eval_bigstep.ENat)
    show "located (S (Loc (l, Amount n)))" by simp
    show "test \<Gamma> (\<mu>, \<rho>(l \<mapsto> Res (natural, Num n)))" using Nat
      apply (auto simp: test_def)
      by (smt Nat.prems \<open>l \<notin> dom \<rho>\<close> domI env_select_compat_def fun_upd_other map_le_def select_preserve_test)
  qed
next
  case (Bool \<Gamma> f b)
  then obtain "l" where "l \<notin> dom \<rho>" using gen_loc
    using test_elim(4) by blast 
  show ?case
  proof(intro exI conjI)
    show "<(\<mu>, \<rho>), B b> \<Down> <(\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b))), S (Loc (l, SLoc l))>"
      by (simp add: \<open>l \<notin> dom \<rho>\<close> loc_eval_bigstep.EBool)
    show "located (S (Loc (l, SLoc l)))" by simp
    show "test \<Gamma> (\<mu>, \<rho>(l \<mapsto> Res (boolean, Bool b)))" using Bool
      apply (auto simp: test_def)
      by (smt Bool.prems \<open>l \<notin> dom \<rho>\<close> domI env_select_compat_def fun_upd_other map_le_def select_preserve_test)
  qed
next
  case (Var \<Gamma> x \<tau> m f)
  then obtain l where "\<mu> x = Some l" 
    apply (auto simp: test_def)
    by (metis domD domI mem_Collect_eq surj_pair)
  then show ?case
  proof(intro exI conjI)
    show "< (\<mu>, \<rho>) , S (V x) > \<Down> < (\<mu>, \<rho>), S (Loc l) >"
      by (simp add: \<open>\<mu> x = Some l\<close> loc_eval_bigstep.EVar)
    show "located (S (Loc l))" by simp
    show "test (\<Gamma>(V x \<mapsto> f \<tau>)) (\<mu>, \<rho>)" using Var
      apply (auto simp: test_def env_select_compat_def)
      by (metis select.simps(1) surj_pair type_preserving_ty_res_compat)
  qed
next
  case (Loc \<Gamma> l \<tau> m f)
  then show ?case
  proof(intro exI conjI)
    show "< (\<mu>, \<rho>) , S (Loc l) > \<Down> < (\<mu>, \<rho>) , S (Loc l) >"
      by (simp add: ELoc)
    show "located (S (Loc l))" by simp
    show "test (\<Gamma>(Loc l \<mapsto> f \<tau>)) (\<mu>, \<rho>)" using Loc
      apply (auto simp: test_def)
      by (smt env_select_compat_def fun_upd_apply option.inject type_preserving_ty_res_compat)
  qed
next
  case (VarDef x \<Gamma> f t)
  then obtain "l" where "l \<notin> dom \<rho>" using gen_loc
    using test_elim(4) by blast
  then show ?case 
  proof(intro exI conjI)
    show "< (\<mu>, \<rho>) , var x : t > \<Down> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t))), S (Loc (l, SLoc l)) >"
      by (metis VarDef.hyps VarDef.prems(1) \<open>l \<notin> dom \<rho>\<close> loc_eval_bigstep.EVarDef mem_Collect_eq test_elim(1) var_dom.simps)
    show "located (S (Loc (l, SLoc l)))" by simp
    show "l \<notin> dom \<rho> \<Longrightarrow> test (\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t)))"
    proof(intro testI)
      show "var_dom (\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) = dom (\<mu>(x \<mapsto> (l, SLoc l)))" using VarDef
        by (auto simp: test_def)
      show "\<forall>la. la \<notin> dom (\<rho>(l \<mapsto> Res (t, emptyVal t))) \<longrightarrow> la \<notin> references (\<mu>(x \<mapsto> (l, SLoc l)))"
        using VarDef by (auto simp: test_def)
      show "inj (\<mu>(x \<mapsto> (l, SLoc l)))"
        using VarDef
        apply (auto simp: test_def)
        by (smt \<open>l \<notin> dom \<rho>\<close> fun_upd_apply inj_on_def)
      show "finite (dom (\<rho>(l \<mapsto> Res (t, emptyVal t))))" using VarDef by (auto simp: test_def)
      show "env_select_compat (\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t)))"
        using VarDef.prems \<open>l \<notin> dom \<rho>\<close>
      proof(unfold env_select_compat_def, safe)
        fix xa a b
        assume lookup: "(\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) xa = Some (a, b)"
        show "\<lbrakk>test \<Gamma> (\<mu>, \<rho>); type_preserving f; \<nexists>y. \<rho> l = Some y;
               (\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) xa = Some (a, b)\<rbrakk>
       \<Longrightarrow> (a, b) \<triangleq> select (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> Res (t, emptyVal t))) xa"
        proof(cases "xa = V x")
          case True
          then have "(a,b) = f (TyQuant.empty, t)" using lookup
            by simp
          then show ?thesis using VarDef.prems True
            apply (auto simp: test_def env_select_compat_def)
            by (simp add: base_type_compat_refl type_preserving_ty_res_compat)
        next
          case False
          then obtain \<tau> where "\<Gamma> xa = \<tau>" using lookup
            by simp
          then show ?thesis using VarDef
            apply (unfold test_def)
            by (smt False VarDef.prems(1) \<open>l \<notin> dom \<rho>\<close> domI env_select_compat_def fun_upd_other lookup map_le_def mem_Collect_eq select_preserve_test test_elim(1) test_elim(5) var_dom.elims)
        qed
      qed
    qed
  qed
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case
    using EEmptyList located.simps(2) by blast 
next
  case (ConsList \<Gamma> f \<L> \<tau>' \<Delta> Tail q \<Xi>)

  have "test \<Gamma> (\<mu>, \<rho>)" using ConsList
    by simp
  then obtain \<mu>' \<rho>' L' where "< (\<mu>, \<rho>) , \<L> > \<Down> < (\<mu>', \<rho>') , L' >" and "located L'" and "test \<Delta> (\<mu>',\<rho>')"
    by (metis ConsList.IH(1) ConsList.prems(2))
  then show ?case
    using ConsList.IH(2) ConsList.prems(2) EConsList located.simps(3) by blast
qed

fun temp_update_env :: "Env \<Rightarrow> Env \<Rightarrow> Env" where
  "temp_update_env \<Gamma> \<Delta> (V x) = \<Delta> (V x)"
| "temp_update_env \<Gamma> \<Delta> (Loc l) = (if Loc l \<in> dom \<Gamma> then \<Gamma> (Loc l) else \<Delta> (Loc l))"

lemma temp1:
  assumes "update_locations \<Gamma> f \<LL> = \<Delta>" and "loc_ty_env \<Delta> \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
  shows "update_locations (temp_update_env \<Gamma> \<Delta>') f \<LL> = \<Delta>'"
  using assms
  sorry

lemma temp2:
  assumes "update_locations \<Gamma> f \<LL> = \<Delta>"
      and "compat \<Delta> f \<KK> \<Sigma>"
    shows "compat \<Gamma> f (\<LL> + \<KK>) \<Sigma>"
  using assms
  sorry

lemma located_var_ignore:
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
    and "located L"
    and "loc_ty_env \<Delta> \<subseteq>\<^sub>m loc_ty_env \<Delta>'"
  shows "(temp_update_env \<Gamma> \<Delta>') \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>'"
  using assms
  sorry
  
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
    sorry

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using ENat.prems using loc_type.cases by blast

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    sorry

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
    sorry

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using EBool.prems using loc_type.cases by blast

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    sorry

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' f (locations (S ?\<L>')) (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "var_ty_env \<Delta> = var_ty_env \<Delta>'"
      and "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env \<Gamma>'"
    using compat typed var_ty_same loc_ty_sub by auto
  then show ?case using EBool.prems by auto
next
  case (EVar \<mu> x l \<rho>)
  then have x_ty: "\<Gamma> (V x) = Some \<tau>"
    sorry

  let ?\<L>' = "Loc l"
  let ?\<Gamma>' = "if ?\<L>' \<in> dom \<Delta> then \<Delta> else \<Delta>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"

  (* TODO: Need to simplify this... *)
  have "\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>" using EVar 
    by (auto simp: compat_def var_store_sync_def)

  from EVar have final_env: "\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)" 
    sorry

  then have var_ty_same: "var_ty_env \<Delta> = var_ty_env ?\<Delta>'" using final_env by simp

  have loc_ty_sub: "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
    sorry

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
  then show ?case sorry
(*
  then have final_env: "\<Delta> = \<Gamma>(V x \<mapsto> f (empty,t))" by simp (erule loc_type.cases, auto)
  let ?\<Gamma>' = "\<Delta>(Loc (l, SLoc l) \<mapsto> (empty,t))"
  let ?\<Delta>' = "?\<Gamma>'(Loc (l, SLoc l) \<mapsto> f (empty,t))"
  let ?\<mu>' = "\<mu>(x \<mapsto> (l, SLoc l))"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (t, emptyVal t))"
  let ?\<L>' = "Loc (l, SLoc l)"

  have compat: "compat ?\<Delta>' f {#} (?\<mu>', ?\<rho>')" 
    using EVarDef final_env
    apply (auto simp: compat_def var_store_sync_def)
    apply (metis (no_types, lifting) domI fun_upd_triv map_le_imp_upd_le option.simps(5) select_loc_le upd_None_map_le)
    apply (smt EVarDef.hyps(2) fun_upd_apply inj_def)
    apply (metis base_type_compat_refl old.prod.inject type_preserving_works)
    apply (metis base_type_compat_refl old.prod.inject type_preserving_works)
    by (smt EVarDef.hyps(1) EVarDef.prems(2) domIff fun_upd_triv map_le_imp_upd_le option.discI select_preserve upd_None_map_le)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : (empty,t) \<stileturn> ?\<Delta>'"
    by (meson Loc fun_upd_same)

  then have prf_compat: "prf_compat_simple \<Delta> (?\<mu>', ?\<rho>') ?\<Delta>'" 
    using EVarDef final_env
    using EVar final_env
    apply (intro prf_compat_simpleI)
    by (auto simp: compat_def var_loc_compat_def)

  have "\<tau> = (empty,t)" using EVarDef loc_type.cases by blast

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Delta>' f {#} (?\<mu>', ?\<rho>')"
      and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : (empty,t) \<stileturn> \<Delta>'" 
      and "prf_compat_simple \<Delta> (?\<mu>', ?\<rho>') \<Delta>'" 
    using compat typed prf_compat ..

  then show ?case using EVarDef.prems \<open>\<tau> = (empty,t)\<close> by auto *)
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

  have "update_locations ?\<Gamma>' f (locations \<L>) = \<Delta>'" using a2
    using \<open>loc_ty_env \<Delta>'' \<subseteq>\<^sub>m loc_ty_env \<Delta>'\<close> temp1 by auto

  then show ?case
  proof(intro exI conjI)
    (* TODO: Cleanup *)

    show "Psamathe.compat ?\<Gamma>' f (locations [ \<tau>' ; \<L> , Tail' ]) \<Sigma>'"
      apply simp
      by (simp add: \<open>update_locations (temp_update_env \<Gamma> \<Delta>') f (locations \<L>) = \<Delta>'\<close> temp2 temp_compat)

    show "var_ty_env \<Delta> = var_ty_env \<Xi>" using \<open>var_ty_env \<Delta> = var_ty_env \<Xi>\<close> by simp

    show "?\<Gamma>' \<turnstile>{s} f ; [ \<tau>' ; \<L> , Tail' ] : \<tau> \<stileturn> \<Xi>"
      using ConsList \<open>\<Delta>' \<turnstile>{s} f ; Tail' : (q, table [] \<tau>') \<stileturn> \<Xi>\<close> \<open>\<tau> = (one \<oplus> q, table [] \<tau>')\<close> \<open>(temp_update_env \<Gamma> \<Delta>') \<turnstile>{s} f ; \<L> : \<tau>' \<stileturn> \<Delta>'\<close> by auto

    show "loc_ty_env \<Gamma> \<subseteq>\<^sub>m loc_ty_env ?\<Gamma>'"
      by (auto simp: map_le_def)
qed

end
