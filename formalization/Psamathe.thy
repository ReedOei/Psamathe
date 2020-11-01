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

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ : _ ; _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} (N n) : (toQuant(n), natural) ; f \<stileturn> \<Gamma>"
| Bool: "\<Gamma> \<turnstile>{s} (B b) : (one, boolean) ; f \<stileturn> \<Gamma>"
| Var: "\<lbrakk> \<Gamma> x = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} (S x) : \<tau> ; f \<stileturn> (\<Gamma>(x \<mapsto> f(\<tau>)))"
| VarDef: "\<lbrakk> V x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} (var x : t) : (empty, t) ; f \<stileturn> (\<Gamma>(V x \<mapsto> f(empty, t)))"
| EmptyList: "\<Gamma> \<turnstile>{s} [ \<tau> ; ] : (empty, table [] \<tau>) ; f \<stileturn> \<Gamma>"
| ConsList: "\<lbrakk> \<Gamma> \<turnstile>{s} \<L> : \<tau> ; f \<stileturn> \<Delta> ;
              \<Delta> \<turnstile>{s} Tail : (q, table [] \<tau>) ; f \<stileturn> \<Xi> \<rbrakk> 
             \<Longrightarrow> \<Gamma> \<turnstile>{s} [ \<tau> ; \<L>, Tail ] : (one \<oplus> q, table [] \<tau>) ; f \<stileturn> \<Xi>"

datatype Val = Num nat | Bool bool 
  | Table "StorageLoc list"
  | error
type_synonym Resource = "BaseTy \<times> Val"
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
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (natural, Num n))), S (Loc (l, Amount n)) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b))), S (Loc (l, SLoc l)) >"
| EVar: "\<lbrakk> \<mu> x = Some l \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), S (V x) > \<rightarrow> < (\<mu>, \<rho>), S (Loc l) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))), S (Loc (l, SLoc l)) >"
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

definition var_dom :: "Env \<Rightarrow> string set" where
  "var_dom \<Gamma> \<equiv> { x . V x \<in> dom \<Gamma> }"

(* This is a weaker version of compatibility (tentatively, locator compatibility)
  This is needed, because while evaluating locators, the type environments won't agree with the 
  actual state of the store (TODO: Could resolve this by going to old updater system),
  because the type environment represents the state of the store *after* the flow occurs. 
  So we will need some separate "statement compatibility" definition, which includes stronger
  conditions on the state of the store (e.g., type quantities being correct, the only strengthening
  I think we will need)*)
fun compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" ("_ \<leftrightarrow> _") where
  "compat \<Gamma> (\<mu>, \<rho>) = ((var_dom \<Gamma> = dom \<mu>) \<and> 
                      (\<forall>x l k. \<mu> x = Some (l, k) \<longrightarrow> \<rho> l \<noteq> None) \<and>
                      (\<forall>x q t. \<Gamma>(V x) = Some (q,t) \<longrightarrow> (\<exists>l v. \<rho> l = Some (t, v))))" 

(* Might not work. 
The type rule gives the type environment after the entire thing has been evaluated, not one step...
lemma compat_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>" and "\<Sigma>" and "\<Sigma>'" and "\<L>'" and "m"
  assumes "< \<Sigma>, \<L> > \<rightarrow> < \<Sigma>', \<L>' >"
      and "\<Gamma> \<turnstile>{m} \<L> : \<tau> ; f \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> \<Sigma>"
    shows "\<Delta> \<leftrightarrow> \<Sigma>'"
  using assms
proof(induction arbitrary: \<Gamma> \<Delta> \<tau> f m rule: loc_eval.induct)
  case (ENat l \<rho> \<mu> n)
  then show ?case
(* TODO: Why do I have to write it like this? *)
    by simp (erule loc_type.cases, auto)
next
  case (EBool l \<rho> \<mu> b)
  then show ?case
    by simp (erule loc_type.cases, auto)
next
  case (EVar \<mu> x l \<rho>)
  then show ?case 
    by simp (erule loc_type.cases, auto simp: var_dom_def)
next
  case (EVarDef x \<mu> l \<rho> t)
  then show ?case
    by simp (erule loc_type.cases, auto simp: var_dom_def)
next
  case (EConsListHeadCongr \<Sigma> \<L> \<Sigma>' \<L>' \<tau>' Tail)
  then have eval: "< \<Sigma> , \<L> > \<rightarrow> < \<Sigma>' , \<L>' >"
    and induct: "\<And>\<Gamma>' \<Delta>' m \<sigma> g. \<lbrakk>\<Gamma>' \<turnstile>{m} \<L> : \<sigma> ; g \<stileturn> \<Delta>'; \<Gamma>' \<leftrightarrow> \<Sigma>\<rbrakk> \<Longrightarrow> \<Delta>' \<leftrightarrow> \<Sigma>'"
    and typed: "\<Gamma> \<turnstile>{m} [ \<tau>' ; \<L> , Tail ] : \<tau> ; f \<stileturn> \<Delta>"
    and compat: "\<Gamma> \<leftrightarrow> \<Sigma>"
    by auto

  (* Why does this need to be split into so many steps... *)
  have "\<Gamma> \<turnstile>{m} [ \<tau>' ; \<L> , Tail ] : \<tau> ; f \<stileturn> \<Delta> \<Longrightarrow> \<exists>\<Delta>'. (\<Gamma> \<turnstile>{m} \<L> : \<tau>' ; f \<stileturn> \<Delta>') \<and> (\<exists>q. (\<Delta>' \<turnstile>{m} Tail : (q, table [] \<tau>') ; f \<stileturn> \<Delta>))"
    apply (erule loc_type.cases)
    by auto
  from this and typed have "\<exists>\<Delta>'. (\<Gamma> \<turnstile>{m} \<L> : \<tau>' ; f \<stileturn> \<Delta>') \<and> (\<exists>q. (\<Delta>' \<turnstile>{m} Tail : (q, table [] \<tau>') ; f \<stileturn> \<Delta>))" 
    by auto
  then obtain \<Delta>' and q 
    where loc_type_env: "\<Gamma> \<turnstile>{m} \<L> : \<tau>' ; f \<stileturn> \<Delta>'" 
    and   tail_type_env: "\<Delta>' \<turnstile>{m} Tail : (q, table [] \<tau>') ; f \<stileturn> \<Delta>" by auto

  from compat and induct and loc_type_env have "\<Delta>' \<leftrightarrow> \<Sigma>'" by auto
  from this and induct and tail_type_env have "\<Delta> \<leftrightarrow> \<Sigma>'" by auto

  then show ?case
next
  case (EConsListTailCongr \<L> \<Sigma> Tail \<Sigma>' Tail' \<tau>)
  then show ?case sorry
qed *)

lemma gen_loc:
  fixes m :: "(nat, 'a) map"
  assumes is_fin: "finite (dom m)"
  obtains "l" where "l \<notin> dom m"
  using ex_new_if_finite is_fin by auto

lemma located_env_compat:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} \<L> : \<tau> ; f \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> \<Sigma>"
      and "located \<L>"
    shows "\<Delta> \<leftrightarrow> \<Sigma>"
  using assms
proof(induction arbitrary: \<Sigma>)
  case (Nat \<Gamma> n f)
  then show ?case by simp
next
  case (Bool \<Gamma> b f)
  then show ?case by simp
next
  case (Var \<Gamma> x \<tau> m f)
  then show ?case 
  proof(cases x)
    case (V x1)
    then show ?thesis using Var.prems by simp
  next
    case (Loc x2)
    then show ?thesis using Var.prems
      by (cases \<Sigma>, simp add: domIff var_dom_def)+
  qed
next
  case (VarDef x \<Gamma> t f)
  then show ?case by simp 
next
  case (EmptyList \<Gamma> \<tau> f)
  then show ?case by simp
next
  case (ConsList \<Gamma> \<L> \<tau> f \<Delta> Tail q \<Xi>)
  then show ?case by simp 
qed

lemma locator_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>"
  assumes "\<Gamma> \<turnstile>{m} \<L> : \<tau> ; f \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
      and "finite (dom \<rho>)"
  shows "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. <(\<mu>, \<rho>), \<L>> \<rightarrow> <(\<mu>', \<rho>'), \<L>'>)"
(* Premise was too strong, combined elements of progress and preservation...TODO: take some of this
    shows "(located \<L> \<and> (\<Delta> \<leftrightarrow> (\<mu>, \<rho>)) \<and> finite (dom \<rho>))
           \<or> (\<exists>\<mu>' \<rho>' \<L>'. (\<Delta> \<leftrightarrow> (\<mu>', \<rho>')) \<and> finite (dom \<rho>') \<and> < (\<mu>, \<rho>), \<L> > \<rightarrow> < (\<mu>', \<rho>'), \<L>' >)" *)
  using assms
proof(induction arbitrary: \<mu> \<rho> m rule: loc_type.induct)
  case (Nat \<Gamma> n f)
  then show ?case by (meson ENat gen_loc)
next
  case (Bool \<Gamma> b f)
  then show ?case by (meson EBool gen_loc)
next
  case (Var \<Gamma> x \<tau> m f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
        and x_in_env: "\<Gamma> x = Some \<tau>" by auto
  then show ?case 
  proof(cases x)
    case (V x1)
    from this and env_compat and x_in_env 
    have "x1 \<in> dom \<mu>" and eq: "x = V x1" by (auto simp: var_dom_def)
    then obtain k where in_lookup: "\<mu> x1 = Some k" by auto
    show ?thesis
    proof(rule disjI2, (rule exI)+)
      from in_lookup and eq show "< (\<mu>, \<rho>) , S x > \<rightarrow> < (\<mu>, \<rho>) , S (Loc k) >"
        by (simp add: EVar) 
    qed
  next
    case (Loc x2)
    then show ?thesis by simp
  qed
next
  case (VarDef x \<Gamma> t f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and "finite (dom \<rho>)"
        and not_in_lookup: "x \<notin> dom \<mu>" by (auto simp: var_dom_def)
  then obtain l where has_loc: "l \<notin> dom \<rho>" using gen_loc by blast
  show ?case
  proof(rule disjI2, (rule exI)+)
    from not_in_lookup and has_loc
    show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))) , S (Loc (l, SLoc l)) >"
      by (rule EVarDef)
  qed
next
  case (EmptyList \<Gamma> \<tau> f)
  then show ?case by simp
next
  case (ConsList \<Gamma> \<L> \<tau> f \<Delta> Tail q \<Xi>)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and loc_typed: "\<Gamma> \<turnstile>{s} \<L> : \<tau> ; f \<stileturn> \<Delta>"
        and tail_typed: "\<Delta> \<turnstile>{s} Tail : (q, table [] \<tau>) ; f \<stileturn> \<Xi>"
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
      from loc_typed and env_compat and loc_l have "\<Delta> \<leftrightarrow> (\<mu>, \<rho>)" using located_env_compat
        by blast
      then have "\<exists>\<mu>' \<rho>' Tail'. < (\<mu>, \<rho>) , Tail > \<rightarrow> < (\<mu>', \<rho>') , Tail' >"
        using tail_induct ConsList.prems(2) False by blast
      then show ?thesis
        using EConsListTailCongr loc_l by blast
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
      and "\<Gamma> \<turnstile>{s} \<L> : \<tau> ; (\<lambda>(_, t'). (empty, t')) \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> \<Sigma>"
      and "finite_store \<Sigma>"
    shows "finite_store \<Sigma>' 
      \<and> (\<exists>\<Gamma>' \<Delta>'. (\<Gamma>' \<leftrightarrow> \<Sigma>') \<and> (\<Gamma>' \<turnstile>{s} \<L>' : \<tau> ; (\<lambda>(_, t'). (empty, t')) \<stileturn> \<Delta>'))"
(*TODO: We may need some compatibility condition between \<Gamma> and \<Gamma>' and \<Delta> and \<Delta>' *)
  using assms
proof(induction arbitrary: \<Gamma> \<tau> \<Delta>)
case (ENat l \<rho> \<mu> n)
  then show ?case
next
  case (EBool l \<rho> \<mu> b)
  then show ?case sorry
next
  case (EVar \<mu> x l \<rho>)
  then show ?case sorry
next
  case (EVarDef x \<mu> l \<rho> t)
  then show ?case sorry
next
  case (EConsListHeadCongr \<Sigma> \<L> \<Sigma>' \<L>' \<tau> Tail)
  then show ?case sorry
next
  case (EConsListTailCongr \<L> \<Sigma> Tail \<Sigma>' Tail' \<tau>)
  then show ?case sorry
qed

end
