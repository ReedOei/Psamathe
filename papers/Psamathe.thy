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

fun bind_option :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option" where
  "bind_option f x = (case map_option f x of Some b \<Rightarrow> b | _ \<Rightarrow> None)"

fun lookup_var_loc :: "Env \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> (string \<rightharpoonup> Type)" (infix "\<circ>\<^sub>l" 30) where
  "lookup_var_loc \<Gamma> \<mu> = ((\<lambda>l. \<Gamma> (Loc l)) \<circ>\<^sub>m \<mu>)"

(* This is a weaker version of compatibility (tentatively, "locator compatibility")
  This is needed, because while evaluating locators, the type environments won't agree with the 
  actual state of the store,
  because the type environment represents the state of the store *after* the flow occurs. 
  So we will need some separate "statement compatibility" definition, which includes stronger
  conditions on the state of the store (e.g., type quantities being correct, the only strengthening
  I think we will need)*)
(*

definition var_store_sync :: "Env \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> bool" where
  "var_store_sync \<Gamma> \<mu> \<equiv> \<forall>x \<tau>. (\<Gamma> \<circ>\<^sub>l \<mu>) x = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>"
fun compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" ("_ \<leftrightarrow> _") where
  "compat \<Gamma> (\<mu>, \<rho>) = ((var_dom \<Gamma> = dom \<mu>) \<and>
                      (\<forall>x. x \<in> dom \<mu> \<longrightarrow> select (\<mu>,\<rho>) (V x) \<noteq> error) \<and>
                      (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>) \<and>
                      var_store_sync \<Gamma> \<mu> \<and>
                      (\<forall>x \<tau>. \<Gamma> x = Some \<tau> \<longrightarrow> ty_res_compat \<tau> (select (\<mu>, \<rho>) x)))"
                      (*(\<forall>x. exact_type (select (\<mu>, \<rho>) x) \<preceq>\<^sub>\<tau> \<Gamma> x))" *)
*)

definition var_store_sync :: "Env \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> bool" where
  "var_store_sync \<Gamma> f \<LL> \<mu> \<equiv> 
    \<forall>x l \<tau>. (\<mu> x = Some l \<and> \<Gamma> (Loc l) = Some \<tau>) \<longrightarrow> \<Gamma> (V x) = Some ((f^^(count \<LL> l)) \<tau>)"

definition compat :: "Env \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> StorageLoc multiset \<Rightarrow> Store \<Rightarrow> bool" where
  "compat \<Gamma> f \<LL> \<Sigma> \<equiv> case \<Sigma> of (\<mu>, \<rho>) \<Rightarrow> ((var_dom \<Gamma> = dom \<mu>) \<and>
                        (\<forall>x. x \<in> dom \<mu> \<longrightarrow> select (\<mu>,\<rho>) (V x) \<noteq> error) \<and>
                        (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>) \<and>
                        var_store_sync \<Gamma> f \<LL> \<mu> \<and>
                        inj \<mu> \<and>
                        (\<forall>x \<tau>. \<Gamma> x = Some \<tau> \<longrightarrow> ty_res_compat \<tau> (select (\<mu>, \<rho>) x)))"
                        (*(\<forall>x. exact_type (select (\<mu>, \<rho>) x) \<preceq>\<^sub>\<tau> \<Gamma> x))" *)

lemma in_type_env_select:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
      and "x \<in> dom \<Gamma>"
  obtains r where "select (\<mu>, \<rho>) x = Res r"
  using assms
  by (auto simp: compat_def, metis Resource.exhaust that ty_res_compat.simps(2))

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
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
      and "\<mu> x = Some l" 
  obtains r where "selectLoc \<rho> l = Res r"
  using assms
  by (auto simp: compat_def, metis Resource.exhaust domI option.simps(5) that)

lemma in_type_env_compat:
  fixes \<Gamma> \<mu> \<rho> x \<tau>
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)"
    and "\<Gamma> (V x) = Some \<tau>"
  obtains l where "\<mu> x = Some l" and "\<tau> \<triangleq> selectLoc \<rho> l"
  using assms
proof(auto simp: compat_def)
  assume "\<Gamma> (V x) = Some \<tau>" and "{x. V x \<in> dom \<Gamma>} = dom \<mu>"
  then have "x \<in> dom \<mu>" by auto
  then obtain l where "\<mu> x = Some l" and "\<tau> \<triangleq> selectLoc \<rho> l" using assms
    apply (auto simp: compat_def)
    by (metis (no_types, hide_lams) domI option.simps(5) select.simps(1) ty_res_compat.elims(3))
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
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "V x \<in> dom \<Gamma>" and "\<mu> x = Some (l,k)"
  shows "selectLoc \<rho> (l,k) = selectLoc \<rho>' (l,k)"
  using assms
  apply (cases k, auto simp: map_le_def compat_def)
  by metis+

lemma compat_loc_in_env:
  fixes \<Gamma> \<mu> \<rho> l k
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" and "Loc (l,k) \<in> dom \<Gamma>"
  obtains r where "selectLoc \<rho> (l,k) = Res r"
  using assms
  by (metis in_type_env_select select.simps(2))

lemma select_loc_preserve_loc:
  fixes \<Gamma> \<mu> \<rho> \<rho>' l k
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "Loc (l,k) \<in> dom \<Gamma>"
  shows "selectLoc \<rho> (l,k) = selectLoc \<rho>' (l,k)"
  using assms
  apply (cases k, auto simp: map_le_def compat_def)
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
    by (metis (no_types, hide_lams) assms(1) assms(4) option.simps(5) select_loc_preserve_var)
next
  case (Loc x2)
  then obtain l and k where "x2 = (l, k)" by (cases x2)
  then show ?thesis using assms Loc
    apply (simp only: select.simps)
    using select_loc_preserve_loc by blast
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
  assumes "compat \<Gamma> f \<LL> (\<mu>, \<rho>)" and "l \<notin> dom \<rho>"
  shows "Loc (l, k) \<notin> dom \<Gamma>"
  using assms compat_loc_in_env not_err_in_dom
  apply auto
  by (metis Resource.distinct(1) assms(1) assms(2) compat_loc_in_env domI)

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

lemma located_env_compat:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> f (locations \<L> + \<LL>) (\<mu>, \<rho>)"
      and "located \<L>"
      and "\<L> wf"
      and "type_preserving f"
    shows "compat \<Delta> f \<LL> (\<mu>, \<rho>)"
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
      by (metis select.simps(2) surj_pair type_preserving_ty_res_compat)
  next
    case False
    then show ?thesis using Loc
      apply (unfold compat_def, clarsimp, safe)
      apply (simp add: var_store_sync_no_var)
      by (metis select.simps(2) surj_pair type_preserving_ty_res_compat)
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
        and "Psamathe.compat \<Gamma> f (locations \<L> + locations Tail + \<LL>) (\<mu>, \<rho>)"
        by auto
  then have "Psamathe.compat \<Delta> f (locations Tail + \<LL>) (\<mu>, \<rho>)" using ConsList
    apply auto
    apply (erule wf_locator.cases)
    apply auto
    by (simp add: add.assoc)
  then show "Psamathe.compat \<Xi> f \<LL> (\<mu>, \<rho>)" using ConsList
    apply auto
    apply (erule wf_locator.cases)
    by auto
qed

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
  then obtain k where in_lookup: "\<mu> x = Some k" using Var in_type_env_compat by blast
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
        by (metis \<open>\<L> wf\<close> ab_semigroup_add_class.add_ac(1)) 
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
(*
definition proof_compat :: "Env \<Rightarrow> (string \<rightharpoonup> StorageLoc) \<Rightarrow> Env \<Rightarrow> bool" ("_ \<lhd>\<^sup>_ _" 50) where
  "\<Gamma> \<lhd>\<^sup>\<mu> \<Gamma>' \<equiv> var_ty_env \<Gamma> = var_ty_env \<Gamma>' \<and> var_store_sync \<Gamma>' \<mu>
            \<and> (\<forall>x. \<Gamma> (V x) = (\<Gamma> \<circ>\<^sub>l \<mu>) x \<longrightarrow> (\<Gamma> \<circ>\<^sub>l \<mu>) x = (\<Gamma>' \<circ>\<^sub>l \<mu>) x)
            \<and> (\<forall>l. (l \<notin> ran \<mu> \<and> (Loc l) \<in> dom \<Gamma>) \<longrightarrow> \<Gamma> (Loc l) = \<Gamma>' (Loc l))"

lemma proof_compat_works:
  fixes \<Gamma> m f \<L> \<tau> \<Delta> \<mu>
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<lhd>\<^sup>\<mu> \<Gamma>'"
      and "\<L> wf"
    (* shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>') \<and> (\<Delta> \<lhd>\<^sup>\<mu> \<Delta>')" *)
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>')"
  using assms
proof(induction arbitrary: \<Gamma>')
  case (Nat \<Gamma> f n)
  then show ?case using loc_type.Nat by blast
next
  case (Bool \<Gamma> f b)
  then show ?case using loc_type.Bool by blast
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case
  proof(cases x)
    case (V x1)
    then have "\<Gamma>' x = Some \<tau>" using Var
      by (metis proof_compat_def var_ty_env.simps)
    then show ?thesis
      apply (intro exI conjI)
      apply (rule loc_type.Var)
      by simp
(*
      from Var.prems show "\<Gamma>(x \<mapsto> f \<tau>) \<lhd>\<^sup>\<mu> \<Gamma>'(x \<mapsto> f \<tau>)"
        apply (auto simp: proof_compat_def var_store_sync_def map_comp_def)
        apply metis *)
  next
    case (Loc x2)
    then have "\<Gamma>' x = Some \<tau>" using Var
      apply (auto simp: proof_compat_def)
    then show ?thesis using Var 
      apply auto
  qed
next
  case (Loc \<Gamma> l f \<tau> m)
  then show ?case
    (* TODO: Fix this nastiness *)
    by (metis domIff loc_type.Loc map_le_def map_upd_triv option.distinct(1) proof_compat_def) 
next
  case (VarDef x \<Gamma> f t)
  then have "V x \<notin> dom \<Gamma>'" by (auto simp: proof_compat_def)
  then show ?case
  proof(intro exI conjI, rule loc_type.VarDef)
    from VarDef.prems show "\<Gamma>(V x \<mapsto> f (TyQuant.empty, t)) \<lhd> \<Gamma>'(V x \<mapsto> f (TyQuant.empty, t))"
      by (auto simp: proof_compat_def)
  qed
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case using loc_type.EmptyList by blast 
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then obtain "\<Delta>'" and "\<Xi>'" 
    where head_ty: "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" and "\<Delta> \<lhd> \<Delta>'" 
      and tail_ty: "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'" and tail_prf_compat: "\<Xi> \<lhd> \<Xi>'"
    by blast

  then show ?case
  proof(intro exI conjI)
    from head_ty and tail_ty
    show "\<Gamma>' \<turnstile>{s} f ; [ \<tau> ; \<L> , Tail ] : (one \<oplus> q, table [] \<tau>) \<stileturn> \<Xi>'" by (rule loc_type.ConsList)
    from tail_prf_compat show "\<Xi> \<lhd> \<Xi>'" by simp
  qed
qed *)

definition proof_compat :: "Env \<Rightarrow> (StorageLoc set) \<Rightarrow> Env \<Rightarrow> bool" where
  "proof_compat \<Gamma> \<LL> \<Gamma>' \<equiv> var_ty_env \<Gamma> = var_ty_env \<Gamma>'
                        \<and> { l . \<Gamma> (Loc l) \<noteq> \<Gamma>' (Loc l) } \<subseteq> \<LL>"

lemma proof_compat_works:
  fixes \<Gamma> m f \<L> \<tau> \<Delta> \<mu>
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "proof_compat \<Gamma> \<LL> \<Gamma>'"
      and "set_mset (locations \<L>) \<inter> \<LL> = {}"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>') \<and> (proof_compat \<Delta> \<LL> \<Delta>')"
  using assms
proof(induction arbitrary: \<Gamma>' \<LL>)
  case (Nat \<Gamma> f n)
  then show ?case using loc_type.Nat by blast
next
  case (Bool \<Gamma> f b)
  then show ?case using loc_type.Bool by blast
next
  case (Var \<Gamma> x \<tau> m f)
  then have "\<Gamma>' (V x) = Some \<tau>"
    by (metis proof_compat_def var_ty_env.simps)
  then show ?case
  proof(intro exI conjI, rule loc_type.Var)
    from Var.prems show "proof_compat (\<Gamma>(V x \<mapsto> f \<tau>)) \<LL> (\<Gamma>'(V x \<mapsto> f \<tau>))"
      apply (auto simp: proof_compat_def)
      by meson 
  qed
next
  case (Loc \<Gamma> l \<tau> m f)
  then have "\<Gamma>' (Loc l) = Some \<tau>"
    apply (auto simp: proof_compat_def)
    by force
  then show ?case
  proof(intro exI conjI, rule loc_type.Loc)
    from Loc.prems show "proof_compat (\<Gamma>(Loc l \<mapsto> f \<tau>)) \<LL> (\<Gamma>'(Loc l \<mapsto> f \<tau>))"
      by (auto simp: proof_compat_def)
  qed
next
  case (VarDef x \<Gamma> f t)
  then have "V x \<notin> dom \<Gamma>'" 
    apply (auto simp: proof_compat_def)
    by metis
  then show ?case
  proof(intro exI conjI, rule loc_type.VarDef)
    from VarDef.prems show "proof_compat (\<Gamma>(V x \<mapsto> f (TyQuant.empty, t))) \<LL> (\<Gamma>'(V x \<mapsto> f (TyQuant.empty, t)))"
      apply (auto simp: proof_compat_def)
      by meson
  qed
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case using loc_type.EmptyList by blast 
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then have "set_mset (locations \<L>) \<inter> \<LL> = {}" 
        and "set_mset (locations Tail) \<inter> \<LL> = {}" by auto
  from this and ConsList
  obtain "\<Delta>'" and "\<Xi>'" 
    where head_ty: "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" and "proof_compat \<Delta> \<LL> \<Delta>'" 
      and tail_ty: "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'" and tail_prf_compat: "proof_compat \<Xi> \<LL> \<Xi>'"
    by blast

  then show ?case
  proof(intro exI conjI)
    from head_ty and tail_ty
    show "\<Gamma>' \<turnstile>{s} f ; [ \<tau> ; \<L> , Tail ] : (one \<oplus> q, table [] \<tau>) \<stileturn> \<Xi>'" by (rule loc_type.ConsList)
    from tail_prf_compat show "proof_compat \<Xi> \<LL> \<Xi>'" by simp
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
  apply (auto simp: compat_def var_store_sync_def)
  apply (metis domI fun_upd_idem_iff fun_upd_upd option.simps(5) select_loc_le upd_None_map_le)
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
  apply (auto simp: compat_def var_store_sync_def)
  apply (metis domI fun_upd_idem_iff fun_upd_upd option.simps(5) select_loc_le upd_None_map_le)
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
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "var_ty_env \<Gamma> = var_ty_env \<Gamma>'"
      and "L wf"
      and "locations L = {#}"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>') \<and> var_ty_env \<Delta> = var_ty_env \<Delta>'"
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
  then show ?case by auto
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
  then obtain \<Delta>' where "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" and "var_ty_env \<Delta> = var_ty_env \<Delta>'" 
    using ConsList by auto
  then obtain \<Xi>' where "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'" and "var_ty_env \<Xi> = var_ty_env \<Xi>'"
    using ConsList \<open> Tail wf \<close>
    by auto
  then show ?case using ConsList loc_type.ConsList
    apply auto
    using \<open>\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'\<close> loc_type.ConsList by blast
qed

(*
lemma prf_compat_simple_works:
  fixes \<Gamma> m f L \<tau> \<Delta> 
  assumes "\<Gamma> \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<lhd>\<^sup>\<mu> \<Gamma>'"
      and "var_loc_compat \<Gamma> \<mu>"
      and "locations L = {#}"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; L : \<tau> \<stileturn> \<Delta>') \<and> (\<Delta> \<lhd>\<^sup>\<mu> \<Delta>')"
  using assms
proof(induction arbitrary: \<Gamma>' \<mu>)
  case (Nat \<Gamma> f n)
  then show ?case using loc_type.Nat by blast
next
  case (Bool \<Gamma> f b)
  then show ?case using loc_type.Bool by blast
next
  case (Var \<Gamma> x \<tau> m f)
  then have "\<Gamma>' (V x) = Some \<tau>"
    apply (auto simp: prf_compat_simple_def)
    by metis
  then show ?case
  proof(intro exI conjI, rule loc_type.Var)
    show "\<Gamma>(V x \<mapsto> f \<tau>) \<lhd>\<^sup>\<mu> \<Gamma>'(V x \<mapsto> f \<tau>)" using Var
      apply (auto simp: prf_compat_simple_def var_loc_compat_def)
      apply meson
      apply (simp add: prf_compat_upd)
  qed
next
  case (Loc \<Gamma> l \<tau> m f)
  then have "\<Gamma>' (Loc l) = Some \<tau>"
    apply (auto simp: prf_compat_simple_def)
    by (metis domI map_le_def)
  then show ?case
  proof(intro exI conjI, rule loc_type.Loc)
    show "\<Gamma>(Loc l \<mapsto> f \<tau>) \<lhd> \<Gamma>'(Loc l \<mapsto> f \<tau>)" using Loc
      by (simp add: prf_compat_upd)
  qed
next
  case (VarDef x \<Gamma> f t)
  then have "V x \<notin> dom \<Gamma>'" 
    by (auto simp: prf_compat_simple_def)
  then show ?case
  proof(intro exI conjI, rule loc_type.VarDef)
    show "\<Gamma>(V x \<mapsto> f (empty, t)) \<lhd> \<Gamma>'(V x \<mapsto> f (empty, t))" using VarDef
      by (simp add: prf_compat_upd)
  qed
next
  case (EmptyList \<Gamma> f \<tau>)
  then show ?case using loc_type.EmptyList by blast 
next
  case (ConsList \<Gamma> f \<L> \<tau> \<Delta> Tail q \<Xi>)
  then obtain \<Delta>' where head_ty: "\<Gamma>' \<turnstile>{s} f ; \<L> : \<tau> \<stileturn> \<Delta>'" and "\<Delta> \<lhd> \<Delta>'"
    by auto
  then obtain \<Xi>' where tail_ty: "\<Delta>' \<turnstile>{s} f ; Tail : (q, table [] \<tau>) \<stileturn> \<Xi>'" and "\<Xi> \<lhd> \<Xi>'"
    using ConsList by auto

  then show ?case
  proof(intro exI conjI)
    from head_ty and tail_ty
    show "\<Gamma>' \<turnstile>{s} f ; [ \<tau> ; \<L> , Tail ] : (one \<oplus> q, table [] \<tau>) \<stileturn> \<Xi>'" by (rule loc_type.ConsList)
    show "\<lbrakk>\<Xi> \<lhd> \<Xi>'\<rbrakk> \<Longrightarrow> \<Xi> \<lhd> \<Xi>'" by simp
  qed
qed *)

lemma var_loc_compat_upd:
  assumes "var_loc_compat \<Gamma> (\<mu>, \<rho>)"
      and "\<mu> x = Some l"
      and "inj \<mu>"
    shows "var_loc_compat (\<Gamma>(V x \<mapsto> \<tau>, Loc l \<mapsto> \<tau>)) (\<mu>, \<rho>)"
  using assms
  apply (auto simp: var_loc_compat_def)
  by (simp add: injD)

lemma locator_preservation:
  fixes "\<Sigma>" and "\<L>" and "\<Sigma>'" and "\<L>'"
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
(* NOTE: compat can take a function from Vars/Locs to updaters (default to id) instead of a single function,
          this may let us get rid of some of the issues we face due to the updater changing throughout 
          the rules ... *)
      and "compat \<Gamma> f {#} \<Sigma>"
      and "finite_store \<Sigma>"
      and "type_preserving f"
      and "var_loc_compat \<Gamma> \<Sigma>"
    shows "finite_store \<Sigma>' 
      \<and> (\<exists>\<Gamma>' \<Delta>'. compat \<Delta>' f {#} \<Sigma>'
                \<and> prf_compat_simple \<Delta> \<Sigma>' \<Delta>'
                \<and> (\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau> \<stileturn> \<Delta>'))"
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
  have compat: "compat ?\<Delta>' f {#} (\<mu>, ?\<rho>')" using ENat
    using \<open>\<tau> = (toQuant n, natural)\<close> add_fresh_num fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (auto simp: compat_def)
    using select_loc_update apply auto[1]
    apply (smt ENat.hyps var_store_sync_def Stored.distinct(1) Stored.inject(2) count_eq_zero_iff insert_noteq_member map_upd_Some_unfold mset_add zero_multiset.rep_eq)
    apply (metis base_type_compat_refl ty_res_compat.simps(1) type_preserving_ty_res_compat)
    by (metis (no_types, lifting) ENat.prems(2) domI finite_map_freshness fun_upd_triv infinite_UNIV_listI select_preserve upd_None_map_le)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using ENat.prems using loc_type.cases by blast

  then have prf_compat: "prf_compat_simple \<Delta> (\<mu>, ?\<rho>') ?\<Delta>'"
    using \<open> l \<notin> dom \<rho> \<close> ENat
    apply (intro prf_compat_simpleI)
    by (auto simp: var_loc_compat_def compat_def var_store_sync_def)

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Delta>' f {#} (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "prf_compat_simple \<Delta> (\<mu>, ?\<rho>') \<Delta>'" 
    using compat typed prf_compat ..
  then show ?case using ENat.prems by auto
next
  case (EBool l \<rho> \<mu> b)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (boolean, Bool b))" by (auto simp: map_le_def) 
  have "\<tau> = (any, boolean)" using EBool loc_type.cases by blast
  let ?\<L>' = "Loc (l, SLoc l)"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (boolean, Bool b))"
  have compat: "compat ?\<Delta>' f {#} (\<mu>, ?\<rho>')" using EBool
    using \<open>\<tau> = (any, boolean)\<close> add_fresh_loc fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (cases b)
    apply (auto simp: compat_def)
    using select_loc_update apply auto[1]
    apply (smt EBool.hyps var_store_sync_def Stored.distinct(1) Stored.inject(2) count_eq_zero_iff insert_noteq_member map_upd_Some_unfold mset_add zero_multiset.rep_eq)
    apply (metis base_type_compat_refl ty_res_compat.simps(1) type_preserving_ty_res_compat)
    apply (metis (no_types, lifting) EBool.prems(2) domI finite_map_freshness fun_upd_triv infinite_UNIV_listI select_preserve upd_None_map_le)
    using select_loc_le apply auto[1]
    apply (smt EBool.hyps var_store_sync_def Stored.distinct(1) Stored.inject(2) count_eq_zero_iff insert_noteq_member map_upd_Some_unfold mset_add zero_multiset.rep_eq)
    apply (metis base_type_compat_refl ty_res_compat.simps(1) type_preserving_ty_res_compat)
    by (metis (no_types, lifting) EBool.prems(2) domI finite_map_freshness fun_upd_triv infinite_UNIV_listI select_preserve upd_None_map_le)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using EBool.prems using loc_type.cases by blast

  then have prf_compat: "prf_compat_simple \<Delta> (\<mu>, ?\<rho>') ?\<Delta>'"
    using \<open> l \<notin> dom \<rho> \<close> EBool
    apply (intro prf_compat_simpleI)
    by (auto simp: var_loc_compat_def compat_def var_store_sync_def)

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Delta>' f {#} (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "prf_compat_simple \<Delta> (\<mu>, ?\<rho>') \<Delta>'" 
    using compat typed prf_compat .. 
  then show ?case using EBool.prems by auto
next
  case (EVar \<mu> x l \<rho>)
  let ?\<L>' = "Loc l"
  let ?\<Gamma>' = "if ?\<L>' \<in> dom \<Delta> then \<Delta> else \<Delta>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
(* NOTE: Need to make sure we only add the new location to the environment in the case that it's not already there! *)
(* Actually, if it's already there, I think we don't need to change it at all ?  ? ? ? *)

  have x_ty: "\<Gamma> (V x) = Some \<tau>" using EVar
     apply auto
     apply (erule loc_type.cases)
    by auto

  (* TODO: Need to simplify this... *)
  have "\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>" using EVar 
    by (auto simp: compat_def var_store_sync_def)

  from EVar have final_env: "\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)" by simp (erule loc_type.cases, auto)

  then show ?case
  proof(cases "Loc l \<in> dom \<Gamma>")
    case True
      then have a1: "\<Gamma> (V x) = \<Gamma> (Loc l)" using EVar
        using \<open>\<forall>x k \<tau>. \<mu> x = Some k \<and> \<Gamma> (Loc k) = Some \<tau> \<longrightarrow> \<Gamma> (V x) = Some \<tau>\<close>
        by (metis (full_types) domD)
      then have a2: "\<Gamma> (Loc l) = Some \<tau>" using x_ty
        by auto
    
      then have compat: "compat ?\<Delta>' f {#} (\<mu>, \<rho>)" using EVar a1 a2 x_ty final_env
        apply (auto simp: compat_def var_store_sync_def)
        apply (simp add: injD)
        apply (metis (no_types, lifting) EVar.prems(2) in_type_env_compat option.inject type_preserving_ty_res_compat)
        by (smt EVar.prems(2) in_type_env_compat option.simps(5) type_preserving_ty_res_compat)
    
      have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'"
        by (simp add: Loc final_env a2)
    
      then have prf_compat: "prf_compat_simple \<Delta> (\<mu>, \<rho>) ?\<Delta>'" 
        using EVar final_env a2 a1
        apply (intro prf_compat_simpleI)
          apply simp
         defer
         apply simp
        apply (auto simp: compat_def)
        by (simp add: var_loc_compat_upd)
      obtain \<Gamma>' and \<Delta>' 
        where "compat \<Delta>' f {#} (\<mu>, \<rho>)"
          and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'" 
          and "prf_compat_simple \<Delta> (\<mu>, \<rho>) \<Delta>'" 
        using compat typed prf_compat ..
      then show ?thesis using EVar.prems by auto
  next
    case False

    then have compat: "compat ?\<Delta>' f {#} (\<mu>, \<rho>)" using EVar x_ty final_env
      apply (auto simp: compat_def var_store_sync_def)
      apply (simp add: injD)
      apply (smt EVar.prems(2) in_type_env_compat option.simps(5) type_preserving_ty_res_compat)
      by (smt EVar.prems(2) in_type_env_compat option.simps(5) type_preserving_ty_res_compat)

    have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'" using False loc_type.Loc 
      apply (simp add: final_env)
      by (metis fun_upd_same fun_upd_upd)

    then have prf_compat: "prf_compat_simple \<Delta> (\<mu>, \<rho>) ?\<Delta>'" 
      using EVar final_env
      apply (intro prf_compat_simpleI)
      apply (auto simp: compat_def)
      by (simp add: var_loc_compat_upd)

    obtain \<Gamma>' and \<Delta>' 
      where "compat \<Delta>' f {#} (\<mu>, \<rho>)"
        and "\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>'" 
        and "prf_compat_simple \<Delta> (\<mu>, \<rho>) \<Delta>'" 
      using compat typed prf_compat ..

      then show ?thesis using EVar.prems by auto
  qed
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

(*

lemma locator_preservation:
  fixes "\<Sigma>" and "\<L>" and "\<Sigma>'" and "\<L>'"
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "compat \<Gamma> f \<LL> \<Sigma>"
      and "set_mset \<LL> \<subseteq> { l . Loc l \<in> dom \<Gamma> }"
      and "finite_store \<Sigma>"
      and "type_preserving f"
    shows "finite_store \<Sigma>' 
      \<and> (\<exists>\<Gamma>' \<Delta>'. compat \<Gamma>' f (\<LL> - locations \<L>') \<Sigma>' 
                \<and> proof_compat \<Delta> (set_mset (locations \<L>')) \<Delta>' 
                \<and> (\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau> \<stileturn> \<Delta>') )"
  using assms
proof(induction arbitrary: \<Gamma> \<tau> f m \<Delta> \<LL>)
  (* TODO: This is an absurd amount of effort for a relatively easy case... *)
  case (ENat l \<rho> \<mu> n)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (natural, Num n))" by (auto simp: map_le_def) 
  have "\<tau> = (toQuant n, natural)" using ENat loc_type.cases by blast
  let ?\<L>' = "Loc (l, Amount n)"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (natural, Num n))"
  have compat: "compat ?\<Gamma>' f (\<LL> - locations (S ?\<L>')) (\<mu>, ?\<rho>')" using ENat
    using \<open>\<tau> = (toQuant n, natural)\<close> add_fresh_num fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (auto simp: compat_def var_store_sync_def)
    using select_loc_update apply auto[1]
    by (metis (no_types, lifting) ENat.prems(2) domI finite_map_freshness fun_upd_triv infinite_UNIV_listI select_preserve upd_None_map_le)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using ENat.prems using loc_type.cases by blast

  then have prf_compat: "proof_compat \<Delta> (set_mset (locations (S ?\<L>'))) ?\<Delta>'" 
    using \<open> l \<notin> dom \<rho> \<close>
    by (auto simp: proof_compat_def)

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' f (\<LL> - locations (S ?\<L>')) (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "proof_compat \<Delta> (set_mset (locations (S  ?\<L>'))) \<Delta>'" 
    using compat typed prf_compat ..
  then show ?case using ENat.prems by auto
next
  case (EBool l \<rho> \<mu> b)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (boolean, Bool b))" by (auto simp: map_le_def) 
  have "\<tau> = (any, boolean)" using EBool loc_type.cases by blast
  let ?\<L>' = "Loc (l, SLoc l)"
  let ?\<Gamma>' = "\<Gamma>(?\<L>' \<mapsto> \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(?\<L>' \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (boolean, Bool b))"
  have compat: "compat ?\<Gamma>' f (\<LL> - locations (S ?\<L>')) (\<mu>, ?\<rho>')" using EBool
    using \<open>\<tau> = (any, boolean)\<close> add_fresh_loc fresh_loc_not_in_env \<open> \<rho> \<subseteq>\<^sub>m ?\<rho>' \<close>
    apply (cases b)
    apply (auto simp: compat_def var_store_sync_def)
    using select_loc_update apply auto[1]
    apply (metis (no_types, lifting) EBool.prems(2) domI finite_map_freshness fun_upd_triv infinite_UNIV_listI select_preserve upd_None_map_le)
    using select_loc_update apply auto[1]
    by (metis (no_types, lifting) EBool.prems(2) domI finite_map_freshness fun_upd_triv infinite_UNIV_listI select_preserve upd_None_map_le)

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> ?\<Delta>'"
    by (metis Loc fun_upd_same)
  have "\<Delta> = \<Gamma>" using EBool.prems using loc_type.cases by blast

  then have prf_compat: "proof_compat \<Delta> (set_mset (locations (S ?\<L>'))) ?\<Delta>'" 
    using \<open> l \<notin> dom \<rho> \<close>
    by (auto simp: proof_compat_def)

  obtain \<Gamma>' and \<Delta>'
    where "compat \<Gamma>' f (\<LL> - locations (S ?\<L>')) (\<mu>, ?\<rho>')"
      and "(\<Gamma>' \<turnstile>{s} f ; S ?\<L>' : \<tau> \<stileturn> \<Delta>')"
      and "proof_compat \<Delta> (set_mset (locations (S  ?\<L>'))) \<Delta>'" 
    using compat typed prf_compat ..
  then show ?case using EBool.prems by auto
next
  case (EVar \<mu> x l \<rho>)
  let ?\<Gamma>' = "\<Delta>"
  let ?\<L>' = "Loc l"
(* NOTE: Need to make sure we only add the new location to the environment in the case that it's not already there! *)
(* Actually, if it's already there, I think we don't need to change it at all ?  ? ? ? *)
  from EVar have "\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)" by simp (erule loc_type.cases, auto)
  then have compat: "compat ?\<Gamma>' f (\<LL> - locations (S ?\<L>')) (\<mu>, \<rho>)" using EVar
    apply (auto simp: compat_def var_store_sync_def)
  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc l) : \<tau> \<stileturn> ?\<Delta>'" by (meson Var fun_upd_same)
  then have prf_compat: "\<Delta> \<lhd> ?\<Delta>'" using EVar \<open>\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)\<close>
    apply (simp add: proof_compat_def map_le_def)
    apply auto
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
*)

end
