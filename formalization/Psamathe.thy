theory Psamathe
  imports Main
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = natural | boolean
type_synonym Type = "TyQuant \<times> BaseTy"
datatype Mode = s | d
datatype SVal = SLoc nat | Amount nat
type_synonym StorageLoc = "nat \<times> SVal" 
datatype Stored = V string | Loc StorageLoc
datatype Locator = N nat | B bool | S Stored
                 | VDef string BaseTy ("var _ : _")
datatype Stmt = Flow Locator Locator
datatype Prog = Prog "Stmt list"

type_synonym Env = "(Stored, Type) map"

definition toQuant :: "nat \<Rightarrow> TyQuant" where
  "toQuant n \<equiv> (if n = 0 then empty else if n = 1 then one else nonempty)"

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ : _ ; _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} (N n) : (toQuant(n), natural) ; f \<stileturn> \<Gamma>"
| Bool: "\<Gamma> \<turnstile>{s} (B b) : (one, boolean) ; f \<stileturn> \<Gamma>"
| Var: "\<lbrakk> \<Gamma> x = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} (S x) : \<tau> ; f \<stileturn> (\<Gamma>(x \<mapsto> f(\<tau>)))"
| VarDef: "\<lbrakk> V x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} (var x : t) : (empty, t) ; f \<stileturn> (\<Gamma>(V x \<mapsto> f(empty, t)))"

datatype Val = Num nat | Bool bool | error
type_synonym Resource = "BaseTy \<times> Val"
type_synonym Store = "(string, StorageLoc) map \<times> (nat, Resource) map"

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal natural = Num 0"
| "emptyVal boolean = Bool False"

inductive loc_eval :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> Locator \<Rightarrow> bool"
  ("< _ , _ > \<rightarrow> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (natural, Num n))), S (Loc (l, Amount n)) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b))), S (Loc (l, SLoc l)) >"
| EVar: "\<lbrakk> \<mu> x = Some l \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), S (V x) > \<rightarrow> < (\<mu>, \<rho>), S (Loc l) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))), S (Loc (l, SLoc l)) >"

fun addQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> TyQuant" ("_ \<oplus> _") where
  "(q \<oplus> empty) = q"
| "(empty \<oplus> q) = q"
| "(nonempty \<oplus> r) = nonempty"
| "(r \<oplus> nonempty) = nonempty"
| "(one \<oplus> r) = nonempty"
| "(r \<oplus> one) = nonempty"
| "(any \<oplus> any) = any"

definition var_dom :: "Env \<Rightarrow> string set" where
  "var_dom \<Gamma> \<equiv> { x . V x \<in> dom \<Gamma> }"

fun compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" ("_ \<leftrightarrow> _") where
  "compat \<Gamma> (\<mu>, \<rho>) = ((var_dom \<Gamma> = dom \<mu>) \<and> 
                      (\<forall>x l k. \<mu> x = Some (l, k) \<longrightarrow> \<rho> l \<noteq> None))"
                      (* (\<forall>x q t. \<Gamma>(V x) = Some (q,t) \<longrightarrow> (\<exists>l v. \<rho> l = Some (t, v))))" *)

definition located :: "Locator \<Rightarrow> bool" where
  "located \<L> \<equiv> case \<L> of S (Loc _) \<Rightarrow> True | _ \<Rightarrow> False"

lemma locator_progress:
  fixes "\<Gamma>" and "\<L>" and "\<tau>" and "\<Delta>" and "\<mu>" and "\<rho>" and "l"
  assumes "\<Gamma> \<turnstile>{s} \<L> : \<tau> ; (\<lambda>(_, t'). (empty, t')) \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
      and "l \<notin> dom \<rho>" (* For convenience only *)
   shows "located \<L> \<or> (\<exists>\<mu>' \<rho>' \<L>'. (\<Delta> \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>), \<L> > \<rightarrow> < (\<mu>', \<rho>'), \<L>' >)"
  using assms
proof(induction rule: loc_type.induct)
  case (Nat \<Gamma> n f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and has_loc: "l \<notin> dom \<rho>" by auto
  show ?case
  proof(rule disjI2,
        rule exI[where x = "\<mu>"], 
        rule exI[where x = "\<rho>(l \<mapsto> (natural, Num n))"], 
        rule exI[where x = "S (Loc (l, Amount n))"],
        rule conjI)
    from env_compat show "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> (natural, Num n)))" by auto
    from has_loc show " < (\<mu>, \<rho>) , N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (natural, Num n))) , S (Loc (l, Amount n)) >"
      by (rule ENat)
  qed
next
  case (Bool \<Gamma> b f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and has_loc: "l \<notin> dom \<rho>" by auto
  show ?case
  proof(rule disjI2,
        rule exI[where x = "\<mu>"], 
        rule exI[where x = "\<rho>(l \<mapsto> (boolean, Bool b))"], 
        rule exI[where x = "S (Loc (l, SLoc l))"],
        rule conjI)
    from env_compat show "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b)))" by auto
    from has_loc show " < (\<mu>, \<rho>) , B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b))) , S (Loc (l, SLoc l)) >"
      by (rule EBool)
  qed
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
    proof(rule disjI2,
          rule exI[where x = "\<mu>"],
          rule exI[where x = "\<rho>"],
          rule exI[where x = "S (Loc k)"],
          rule conjI)
      from env_compat and x_in_env show "\<Gamma>(x \<mapsto> f(\<tau>)) \<leftrightarrow> (\<mu>, \<rho>)" by (auto simp: var_dom_def)
      from in_lookup and eq show "< (\<mu>, \<rho>) , S x > \<rightarrow> < (\<mu>, \<rho>) , S (Loc k) >" 
        apply auto
        by (rule EVar, auto)
    qed
  next
    case (Loc x2)
    then have eq: "x = Loc x2" by auto
    show ?thesis
    proof(rule disjI1)
      from eq show "located (S x)" by (auto simp: located_def)
    qed
  qed
next
  case (VarDef x \<Gamma> t f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and has_loc: "l \<notin> dom \<rho>"
        and not_in_lookup: "x \<notin> dom \<mu>" by (auto simp: var_dom_def)
  show ?case
  proof(rule disjI2,
        rule exI[where x = "\<mu>(x \<mapsto> (l, SLoc l))"],
        rule exI[where x = "\<rho>(l \<mapsto> (t, emptyVal t))"],
        rule exI[where x = "S (Loc (l, SLoc l))"],
        rule conjI)
    from env_compat show "(\<Gamma>(V x \<mapsto> f (empty, t))) \<leftrightarrow> (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t)))"
      by (auto simp: var_dom_def)
    from not_in_lookup and has_loc
    show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))) , S (Loc (l, SLoc l)) >"
      by (rule EVarDef)
  qed
qed

end
