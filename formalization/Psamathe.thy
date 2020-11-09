theory Psamathe
  imports Main
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
| Var: "\<lbrakk> \<Gamma> (V x) = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (V x)) : \<tau> \<stileturn> (\<Gamma>(V x \<mapsto> f(\<tau>)))"
| Loc: "\<lbrakk> \<Gamma> (Loc l) = Some (f(\<tau>)) \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} f ; (S (Loc l)) : \<tau> \<stileturn> (\<Gamma>(Loc l \<mapsto> f(\<tau>)))"
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

fun exactType :: "Resource \<Rightarrow> Type option" where
  "exactType (Res (t, Num n)) = Some (toQuant n, t)"
| "exactType (Res (t, Bool b)) = Some (if b then (one, t) else (empty, t))"
| "exactType (Res (t, Table vs)) = Some (toQuant (length vs), t)"
| "exactType error = None"

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

(* This is a weaker version of compatibility (tentatively, "locator compatibility")
  This is needed, because while evaluating locators, the type environments won't agree with the 
  actual state of the store,
  because the type environment represents the state of the store *after* the flow occurs. 
  So we will need some separate "statement compatibility" definition, which includes stronger
  conditions on the state of the store (e.g., type quantities being correct, the only strengthening
  I think we will need)*)
fun compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" ("_ \<leftrightarrow> _") where
  "compat \<Gamma> (\<mu>, \<rho>) = ((var_dom \<Gamma> = dom \<mu>) \<and>
                      (\<forall>x. x \<in> dom \<mu> \<longrightarrow> select (\<mu>,\<rho>) (V x) \<noteq> error) \<and>
                      (\<forall>l. l \<notin> dom \<rho> \<longrightarrow> l \<notin> references \<mu>) \<and>
                      (\<forall>x \<tau>. \<Gamma> x = Some \<tau> \<longrightarrow> ty_res_compat \<tau> (select (\<mu>, \<rho>) x)))"
                      (*(\<forall>x. exactType (select (\<mu>, \<rho>) x) \<preceq>\<^sub>\<tau> \<Gamma> x))" *)
(* TODO: Need to eventually put this next line back. This is the part of type compatibility 
    that I think should be retained by locator evaluation *)

lemma in_type_env_select:
  fixes \<Gamma> \<mu> \<rho> x
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
      and "x \<in> dom \<Gamma>"
  obtains r where "select (\<mu>, \<rho>) x = Res r"
  using assms
  by (auto, metis Resource.exhaust that ty_res_compat.simps(2))

(* TODO: Would like to significantly clean these up (and also some of the other select lemmas) *)

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
    by (metis Resource.simps(5) exactType.cases) (* TODO: why is it using exactType? *)
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
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
      and "\<mu> x = Some l" 
  obtains r where "selectLoc \<rho> l = Res r"
  using assms
  by (auto, metis Resource.exhaust domI option.simps(5) that)

lemma in_type_env_compat:
  fixes \<Gamma> \<mu> \<rho> x \<tau>
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
    and "\<Gamma> (V x) = Some \<tau>"
  obtains l where "\<mu> x = Some l" and "\<tau> \<triangleq> selectLoc \<rho> l"
  using assms
proof(auto)
  assume "\<Gamma> (V x) = Some \<tau>" and "{x. V x \<in> dom \<Gamma>} = dom \<mu>"
  then have "x \<in> dom \<mu>" by auto
  then obtain l where "\<mu> x = Some l" and "\<tau> \<triangleq> selectLoc \<rho> l" using assms
    by (metis compat.simps domD option.simps(5) select.simps(1))
  then show ?thesis using assms \<open>\<mu> x = Some l\<close> that by simp 
qed

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
  then show ?case by simp
next
  case (Loc \<Gamma> l f \<tau> m)
  then have l_in_dom: "Loc l \<in> dom \<Gamma>" by auto
  then obtain \<mu> \<rho> where "\<Sigma> = (\<mu>, \<rho>)" by (cases \<Sigma>)
  then show ?case using Loc by (simp add: fun_upd_idem)
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
  then obtain k where in_lookup: "\<mu> x = Some k"
    by (metis compat.simps domD domI mem_Collect_eq var_dom.simps)
  then show ?case 
  proof(intro disjI2 exI)
    from in_lookup show "< (\<mu>, \<rho>) , S (V x) > \<rightarrow> < (\<mu>, \<rho>) , S (Loc k) >"
      by (simp add: EVar) 
  qed
next
  case (Loc \<Gamma> l f \<tau> m)
  then show ?case by simp
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

definition proof_compat :: "Env \<Rightarrow> Env \<Rightarrow> bool" (infix "\<lhd>" 50) where
  "proof_compat \<Gamma> \<Gamma>' \<equiv> (var_dom \<Gamma> = var_dom \<Gamma>') \<and> \<Gamma> \<subseteq>\<^sub>m \<Gamma>'"

lemma proof_compat_works:
  fixes \<Gamma> m f \<L> \<tau> \<Delta>
  assumes "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<lhd> \<Gamma>'"
    shows "\<exists>\<Delta>'. (\<Gamma>' \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>') \<and> \<Delta> \<lhd> \<Delta>'"
  using assms
proof(induction arbitrary: \<Gamma>')
  case (Nat \<Gamma> f n)
  then show ?case using loc_type.Nat by blast
next
  case (Bool \<Gamma> f b)
  then show ?case using loc_type.Bool by blast
next
  case (Var \<Gamma> x \<tau> m f)
  then have "\<Gamma>' (V x) = Some \<tau>" by (metis proof_compat_def domI map_le_def)
  then show ?case
  proof(intro exI conjI, rule loc_type.Var)
    from Var.prems show "\<Gamma>(V x \<mapsto> f \<tau>) \<lhd> \<Gamma>'(V x \<mapsto> f \<tau>)" by (auto simp: proof_compat_def)
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
qed

definition resource_le :: "(nat \<rightharpoonup> Resource) \<Rightarrow> (nat \<rightharpoonup> Resource) \<Rightarrow> bool" (infix "\<subseteq>\<^sub>r" 50) where
  "\<rho> \<subseteq>\<^sub>r \<rho>' \<equiv> \<rho> \<subseteq>\<^sub>m \<rho>' \<and> (\<forall>n \<in> dom \<rho>' - dom \<rho>. \<exists>r. \<rho>' n = Some (Res r))"

lemma select_loc_le:
  fixes \<rho> \<rho>' l
  assumes "\<rho> \<subseteq>\<^sub>m \<rho>'" and "selectLoc \<rho> l \<noteq> error"
  shows "selectLoc \<rho>' l \<noteq> error"
  using assms 
  apply (auto simp: resource_le_def)
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
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "V x \<in> dom \<Gamma>" and "\<mu> x = Some (l,k)"
  shows "selectLoc \<rho> (l,k) = selectLoc \<rho>' (l,k)"
  using assms
  apply (cases k, auto simp: map_le_def)
  by metis+

lemma compat_loc_in_env:
  fixes \<Gamma> \<mu> \<rho> l k
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" and "Loc (l,k) \<in> dom \<Gamma>"
  obtains r where "selectLoc \<rho> (l,k) = Res r"
  using assms
  by (metis in_type_env_select select.simps(2))

lemma select_loc_preserve_loc:
  fixes \<Gamma> \<mu> \<rho> \<rho>' l k
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "Loc (l,k) \<in> dom \<Gamma>"
  shows "selectLoc \<rho> (l,k) = selectLoc \<rho>' (l,k)"
  using assms
  apply (cases k, auto simp: map_le_def)
  apply (metis domIff option.simps(4) select.simps(2) selectLoc.simps(2) ty_res_compat.simps(2))
   apply (cases "\<rho> l")
  apply auto
  apply fastforce
  apply (metis (no_types, lifting) domI option.simps(5))
  by (metis (no_types, lifting) Resource.distinct(1) assms(1) assms(3) compat_loc_in_env domIff option.simps(4) selectLoc.simps(1))

lemma select_preserve:
  fixes \<Gamma> \<mu> \<rho> \<mu>' \<rho>' x
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" and "\<mu> \<subseteq>\<^sub>m \<mu>'" and "\<rho> \<subseteq>\<^sub>m \<rho>'" and "x \<in> dom \<Gamma>"
  shows "select (\<mu>, \<rho>) x = select (\<mu>', \<rho>') x"
  using assms
proof(cases x)
  case (V x1)
  then have "x1 \<in> dom \<mu>" using assms by auto
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
  assumes "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" and "l \<notin> dom \<rho>"
  shows "Loc (l, k) \<notin> dom \<Gamma>"
  using assms compat_loc_in_env not_err_in_dom
  apply auto
  by (metis Resource.distinct(1) assms(1) assms(2) compat_loc_in_env domI)

lemma locator_preservation:
  fixes "\<Sigma>" and "\<L>" and "\<Sigma>'" and "\<L>'"
  assumes "<\<Sigma>, \<L>> \<rightarrow> <\<Sigma>', \<L>'>"
      and "\<Gamma> \<turnstile>{m} f ; \<L> : \<tau> \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> \<Sigma>"
      and "finite_store \<Sigma>"
      and "type_preserving f"
    shows "finite_store \<Sigma>' 
      \<and> (\<exists>\<Gamma>' \<Delta>'. (\<Gamma>' \<leftrightarrow> \<Sigma>') \<and> (\<Gamma>' \<turnstile>{s} f ; \<L>' : \<tau> \<stileturn> \<Delta>') \<and> \<Delta> \<lhd> \<Delta>')"
  using assms
proof(induction arbitrary: \<Gamma> \<tau> f m \<Delta>)
  (* TODO: This is an absurd amount of effort for a relatively easy case... *)
  case (ENat l \<rho> \<mu> n)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (natural, Num n))" by (auto simp: map_le_def) 
  have "\<tau> = (toQuant n, natural)" using ENat loc_type.cases by blast
  let ?\<Gamma>' = "\<Gamma>(Loc (l, Amount n) \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (natural, Num n))"
  have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>, ?\<rho>')" using ENat
  proof(unfold compat.simps, intro conjI)
    show "var_dom ?\<Gamma>' = dom \<mu>" using ENat by auto
    show "\<forall>x. x \<in> dom \<mu> \<longrightarrow> select (\<mu>, ?\<rho>') (V x) \<noteq> error"
    proof(intro allI impI)
      fix x
      assume "x \<in> dom \<mu>"
      then show "select (\<mu>, ?\<rho>') (V x) \<noteq> error" 
        using in_var_env_select \<open>\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)\<close> \<open>\<rho> \<subseteq>\<^sub>m ?\<rho>'\<close> \<open>x \<in> dom \<mu>\<close>
        by (metis compat.simps map_le_def select_update)
    qed
    have "l \<notin> references \<mu>" using ENat by auto
    then show "\<forall>k. k \<notin> dom ?\<rho>' \<longrightarrow> k \<notin> references \<mu>" using ENat by auto
    show "\<forall>x \<tau>. ?\<Gamma>' x = Some \<tau> \<longrightarrow> \<tau> \<triangleq> select (\<mu>, ?\<rho>') x" 
      using \<open>\<tau> = (toQuant n, natural)\<close> \<open>type_preserving f\<close> \<open>\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)\<close> \<open> l \<notin> references \<mu> \<close>
      apply auto
      apply (metis base_type_compat_refl prod.inject type_preserving_works)
      by (metis ENat.prems(2) \<open>\<rho> \<subseteq>\<^sub>m ?\<rho>'\<close> domI map_le_refl select_preserve)
  qed

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc (l, Amount n)) : \<tau> \<stileturn> ?\<Gamma>'"
    by (metis Loc fun_upd_same fun_upd_upd)
  have "\<Delta> = \<Gamma>" using ENat.prems using loc_type.cases by blast
  then have prf_compat: "\<Delta> \<lhd> ?\<Gamma>'" using \<open> l \<notin> dom \<rho> \<close>
    apply (simp add: proof_compat_def map_le_def)
    using ENat.prems(2) fresh_loc_not_in_env by blast

  obtain \<Gamma>' and \<Delta>'
    where "\<Gamma>' \<leftrightarrow> (\<mu>, ?\<rho>')" 
      and "(\<Gamma>' \<turnstile>{s} f ; S (Loc (l, Amount n)) : \<tau> \<stileturn> \<Delta>')" 
      and "\<Delta> \<lhd> \<Delta>'" using compat typed prf_compat ..
  then show ?case using ENat.prems by auto
next
  case (EBool l \<rho> \<mu> b)
  then have "\<rho> \<subseteq>\<^sub>m \<rho>(l \<mapsto> Res (boolean, Bool b))" by (auto simp: map_le_def) 
  have "\<tau> = (one, boolean)" using EBool loc_type.cases by blast
  let ?\<Gamma>' = "\<Gamma>(Loc (l, SLoc l) \<mapsto> f \<tau>)"
  let ?\<rho>' = "\<rho>(l \<mapsto> Res (boolean, Bool b))"
  have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>, ?\<rho>')" using EBool
  proof(unfold compat.simps, intro conjI)
    show "var_dom ?\<Gamma>' = dom \<mu>" using EBool by auto
    show "\<forall>x. x \<in> dom \<mu> \<longrightarrow> select (\<mu>, ?\<rho>') (V x) \<noteq> error"
    proof(intro allI impI)
      fix x
      assume "x \<in> dom \<mu>"
      then show "select (\<mu>, ?\<rho>') (V x) \<noteq> error" 
        using in_var_env_select \<open>\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)\<close> \<open>\<rho> \<subseteq>\<^sub>m ?\<rho>'\<close> \<open>x \<in> dom \<mu>\<close>
        by (metis compat.simps map_le_def select_update)
    qed
    have "l \<notin> references \<mu>" using EBool by auto
    then show "\<forall>k. k \<notin> dom ?\<rho>' \<longrightarrow> k \<notin> references \<mu>" using EBool by auto
    show "\<forall>x \<tau>. ?\<Gamma>' x = Some \<tau> \<longrightarrow> \<tau> \<triangleq> select (\<mu>, ?\<rho>') x" 
      using \<open>\<tau> = (one, boolean)\<close> \<open>type_preserving f\<close> \<open>\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)\<close> \<open> l \<notin> references \<mu> \<close>
      apply auto
      apply (metis base_type_compat_refl prod.inject type_preserving_works)
      by (metis EBool.prems(2) \<open>\<rho> \<subseteq>\<^sub>m ?\<rho>'\<close> domI map_le_refl select_preserve)
  qed

  have typed: "?\<Gamma>' \<turnstile>{s} f ; S (Loc (l, SLoc l)) : \<tau> \<stileturn> ?\<Gamma>'"
    by (metis Loc fun_upd_same fun_upd_upd)
  have "\<Delta> = \<Gamma>" using EBool.prems using loc_type.cases by blast
  then have prf_compat: "\<Delta> \<lhd> ?\<Gamma>'" using \<open> l \<notin> dom \<rho> \<close>
    apply (simp add: proof_compat_def map_le_def)
    using EBool.prems(2) fresh_loc_not_in_env by blast

  obtain \<Gamma>' and \<Delta>'
    where "\<Gamma>' \<leftrightarrow> (\<mu>, ?\<rho>')" 
      and "(\<Gamma>' \<turnstile>{s} f ; S (Loc (l, SLoc l)) : \<tau> \<stileturn> \<Delta>')" 
      and "\<Delta> \<lhd> \<Delta>'" using compat typed prf_compat ..
  then show ?case using EBool.prems by auto
next
  case (EVar \<mu> x l \<rho>)
  let ?\<Gamma>' = "\<Delta>(Loc l \<mapsto> f \<tau>)"
  let ?\<Delta>' = "?\<Gamma>'(Loc l \<mapsto> f \<tau>)"
  from EVar have "\<Delta> = \<Gamma>(V x \<mapsto> f \<tau>)" by simp (erule loc_type.cases, auto)
  then have compat: "?\<Gamma>' \<leftrightarrow> (\<mu>, \<rho>)" using EVar by auto blast+
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

end
