theory Psamathe
  imports Main
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = natural | boolean
type_synonym Type = "TyQuant \<times> BaseTy"
datatype Mode = s | d
datatype Locator = N nat | B bool | V string 
                 | VDef string BaseTy ("var _ : _")
datatype Stmt = Flow Locator Locator
datatype Prog = Prog "Stmt list"

type_synonym Env = "(string, Type) map"

definition toQuant :: "nat \<Rightarrow> TyQuant" where
  "toQuant n \<equiv> (if n = 0 then empty else if n = 1 then one else nonempty)"

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ : _ ; _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} (N n) : (toQuant(n), natural) ; f \<stileturn> \<Gamma>"
| Bool: "\<Gamma> \<turnstile>{s} (B b) : (one, boolean) ; f \<stileturn> \<Gamma>"
| Var: "\<lbrakk> \<Gamma> x = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{m} (V x) : \<tau> ; f \<stileturn> (\<Gamma>(x \<mapsto> f(\<tau>)))"
| VarDef: "\<lbrakk> x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} (var x : t) : (empty, t) ; f \<stileturn> (\<Gamma>(x \<mapsto> f(empty, t)))"

datatype Val = Num nat | Bool bool | error
datatype Loc = SLoc nat | Amount nat
type_synonym Resource = "BaseTy \<times> Val"
type_synonym Store = "(string, nat \<times> Loc) map \<times> (nat, Resource) map"

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal natural = Num 0"
| "emptyVal boolean = Bool False"

inductive loc_eval :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> (Locator + Loc \<times> Loc) \<Rightarrow> bool"
  ("< _ , _ > \<rightarrow> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (natural, Num n))), Inr (SLoc l, Amount n) >"
| EBool: "\<lbrakk> l \<notin> dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b))), Inr (SLoc l, SLoc l) >"
| EVar: "\<lbrakk> \<mu> x = Some (l, k) \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), V x > \<rightarrow> < (\<mu>, \<rho>), Inr (SLoc l, k) >"
| EVarDef: "\<lbrakk> x \<notin> dom \<mu> ; l \<notin> dom \<rho> \<rbrakk> 
            \<Longrightarrow> < (\<mu>, \<rho>), var x : t > 
                \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))), Inr (SLoc l, SLoc l) >"

fun addQuant :: "TyQuant \<Rightarrow> TyQuant \<Rightarrow> TyQuant" ("_ \<oplus> _") where
  "(q \<oplus> empty) = q"
| "(empty \<oplus> q) = q"
| "(nonempty \<oplus> r) = nonempty"
| "(r \<oplus> nonempty) = nonempty"
| "(one \<oplus> r) = nonempty"
| "(r \<oplus> one) = nonempty"
| "(any \<oplus> any) = any"

fun compat :: "Env \<Rightarrow> Store \<Rightarrow> bool" ("_ \<leftrightarrow> _") where
  "compat \<Gamma> (\<mu>, \<rho>) = ((dom \<Gamma> = Map.dom \<mu>) \<and> 
                      (\<forall>x l k. \<mu> x = Some (l, k) \<longrightarrow> \<rho> l \<noteq> None))"

lemma
  fixes "\<Gamma>" and "\<L>" and "q" and "t" and "\<Delta>" and "\<mu>" and "\<rho>" and "l"
  assumes "\<Gamma> \<turnstile>{s} \<L> : (q,t) ; (\<lambda>(_, t'). (empty, t')) \<stileturn> \<Delta>"
      and "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
      and "l \<notin> Map.dom \<rho>" (* For convenience only *)
   shows "\<exists>\<mu>'. \<exists>\<rho>'. \<exists>\<L>'. (\<Delta> \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>), \<L> > \<rightarrow> < (\<mu>', \<rho>'), \<L>' >"
  using assms
proof(induction rule: loc_type.induct)
  case (Nat \<Gamma> n f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and has_loc: "l \<notin> Map.dom \<rho>" by auto
  then show ?case
  proof - 
    show "\<exists>\<mu>'. \<exists>\<rho>'. \<exists>\<L>'. (\<Gamma> \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>), N n > \<rightarrow> < (\<mu>', \<rho>'), \<L>' >" 
    proof(rule exI[where x = "\<mu>"], 
          rule exI[where x = "\<rho>(l \<mapsto> (natural, Num n))"], 
          rule exI[where x = "Inr (SLoc l, Amount n)"],
          rule conjI)
      from env_compat show "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> (natural, Num n)))" by auto
      from has_loc show " < (\<mu>, \<rho>) , N n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (natural, Num n))) , Inr (SLoc l, Amount n) >"
        by (rule ENat)
    qed
  qed
next
  case (Bool \<Gamma> b f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and has_loc: "l \<notin> Map.dom \<rho>" by auto
  then show ?case
  proof - 
    show "\<exists>\<mu>'. \<exists>\<rho>'. \<exists>\<L>'. (\<Gamma> \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>), B b > \<rightarrow> < (\<mu>', \<rho>'), \<L>' >" 
    proof(rule exI[where x = "\<mu>"], 
          rule exI[where x = "\<rho>(l \<mapsto> (boolean, Bool b))"], 
          rule exI[where x = "Inr (SLoc l, SLoc l)"],
          rule conjI)
      from env_compat show "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b)))" by auto
      from has_loc show " < (\<mu>, \<rho>) , B b > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (boolean, Bool b))) , Inr (SLoc l, SLoc l) >"
        by (rule EBool)
    qed
  qed
next
  case (Var \<Gamma> x \<tau> m f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)"
        and x_in_env: "\<Gamma> x = Some \<tau>" by auto
  then have "x \<in> Map.dom \<mu>" by auto
  then obtain xl and k where in_lookup: "\<mu> x = Some (xl, k)" by auto
  then show ?case
  proof -
    show "\<exists>\<mu>'. \<exists>\<rho>'. \<exists>\<L>'. (\<Gamma>(x \<mapsto> f(\<tau>)) \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>) , V x > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >"
    proof(rule exI[where x = "\<mu>"],
          rule exI[where x = "\<rho>"],
          rule exI[where x = "Inr (SLoc xl, k)"],
          rule conjI)
      from env_compat and x_in_env show "\<Gamma>(x \<mapsto> f(\<tau>)) \<leftrightarrow> (\<mu>, \<rho>)" by auto
      from in_lookup show "< (\<mu>, \<rho>) , V x > \<rightarrow> < (\<mu>, \<rho>) , Inr (SLoc xl, k) >" by (rule EVar)
    qed
  qed
next
  case (VarDef x \<Gamma> t f)
  then have env_compat: "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>)" 
        and has_loc: "l \<notin> Map.dom \<rho>"
        and not_in_lookup: "x \<notin> Map.dom \<mu>" by auto
  then show ?case
  proof -
    show "\<exists>\<mu>' \<rho>' \<L>'. ((\<Gamma>(x \<mapsto> f(empty, t))) \<leftrightarrow> (\<mu>', \<rho>')) \<and> 
                     < (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >"
    proof(rule exI[where x = "\<mu>(x \<mapsto> (l, SLoc l))"],
          rule exI[where x = "\<rho>(l \<mapsto> (t, emptyVal t))"],
          rule exI[where x = "Inr (SLoc l, SLoc l)"],
          rule conjI)
      from env_compat show "(\<Gamma>(x \<mapsto> f (empty, t))) \<leftrightarrow> (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t)))"
        by auto
      from not_in_lookup and has_loc
      show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))) , Inr (SLoc l, SLoc l) >"
        by (rule EVarDef)
    qed
  qed
qed

end
