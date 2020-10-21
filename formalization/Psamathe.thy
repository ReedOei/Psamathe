theory Psamathe
  imports Main
begin

datatype TyQuant = empty | any | one | nonempty
datatype BaseTy = nat
type_synonym Type = "TyQuant \<times> BaseTy"
datatype Mode = s | d
datatype Locator = C nat | V string 
                 | VDef string BaseTy ("var _ : _")
datatype Stmt = Flow Locator Locator
datatype Prog = Prog "Stmt list"

type_synonym Env = "(string \<times> Type) set"

definition toQuant :: "nat \<Rightarrow> TyQuant" where
  "toQuant n \<equiv> (if n = 0 then empty else if n = 1 then one else nonempty)"
definition dom :: "Env \<Rightarrow> string set" where
  "dom \<Gamma> \<equiv> { x . \<exists>\<tau>. (x,\<tau>) \<in> \<Gamma> }"

inductive loc_type :: "Env \<Rightarrow> Mode \<Rightarrow> Locator \<Rightarrow> Type \<Rightarrow> (Type \<Rightarrow> Type) \<Rightarrow> Env \<Rightarrow> bool"
  ("_ \<turnstile>{_} _ : _ ; _ \<stileturn> _") where
  Nat: "\<Gamma> \<turnstile>{s} (C n) : (toQuant(n), nat) ; f \<stileturn> \<Gamma>"
| Var: "(\<Gamma> \<union> {(x, \<tau>)}) \<turnstile>{m} (V x) : \<tau> ; f \<stileturn> (\<Gamma> \<union> {(x, f(\<tau>))})"
| VarDef: "\<lbrakk> x \<notin> dom \<Gamma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>{d} (var x : t) : (empty, t) ; f \<stileturn> (\<Gamma> \<union> {(x, f(empty, t))})"

datatype Val = Num nat | error
datatype Loc = SLoc nat | Amount nat
type_synonym Resource = "BaseTy \<times> Val"
type_synonym Store = "(string, nat \<times> Loc) map \<times> (nat, Resource) map"

fun emptyVal :: "BaseTy \<Rightarrow> Val" where
  "emptyVal nat = Num 0"

inductive loc_eval :: "Store \<Rightarrow> Locator \<Rightarrow> Store \<Rightarrow> (Locator + Loc \<times> Loc) \<Rightarrow> bool"
  ("< _ , _ > \<rightarrow> < _ , _ >") where
  ENat: "\<lbrakk> l \<notin> Map.dom \<rho> \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), C n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (nat, Num n))), Inr (SLoc l, Amount n) >"
| EVar: "\<lbrakk> \<mu> x = Some (l, k) \<rbrakk> \<Longrightarrow> < (\<mu>, \<rho>), V x > \<rightarrow> < (\<mu>, \<rho>), Inr (SLoc l, k) >"
| EVarDef: "\<lbrakk> x \<notin> Map.dom \<mu> ; l \<notin> Map.dom \<rho> \<rbrakk> 
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

lemma dom_insert[simp]: "dom (insert (x, \<tau>) \<Gamma>) = insert x (dom \<Gamma>)"
  by (cases "\<tau>", auto simp: dom_def)

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
    show "\<exists>\<mu>'. \<exists>\<rho>'. \<exists>\<L>'. (\<Gamma> \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>), C n > \<rightarrow> < (\<mu>', \<rho>'), \<L>' >" 
    proof(rule exI[where x = "\<mu>"], 
          rule exI[where x = "\<rho>(l \<mapsto> (nat, Num n))"], 
          rule exI[where x = "Inr (SLoc l, Amount n)"],
          rule conjI)
      from env_compat show "\<Gamma> \<leftrightarrow> (\<mu>, \<rho>(l \<mapsto> (BaseTy.nat, Num n)))" by auto
      from has_loc show " < (\<mu>, \<rho>) , C n > \<rightarrow> < (\<mu>, \<rho>(l \<mapsto> (BaseTy.nat, Num n))) , Inr (SLoc l, Amount n) >"
        by (rule ENat)
    qed
  qed
next
  case (Var \<Gamma> x \<tau> m f)
  then have env_compat: "(\<Gamma> \<union> {(x, \<tau>)}) \<leftrightarrow> (\<mu>, \<rho>)" by auto
  then have "x \<in> Map.dom \<mu>" 
  proof -
    have in_type_env: "x \<in> dom (\<Gamma> \<union> {(x, \<tau>)})" 
      by (simp only: dom_def Set.mem_Collect_eq, rule exI[where x = "\<tau>"], auto)
    from this and env_compat show "x \<in> Map.dom \<mu>" by auto
  qed
  then obtain xl and k where in_lookup: "\<mu> x = Some (xl, k)" by auto
  then show ?case
  proof -
    show "\<exists>\<mu>'. \<exists>\<rho>'. \<exists>\<L>'. ((\<Gamma> \<union> {(x, f \<tau>)}) \<leftrightarrow> (\<mu>', \<rho>')) \<and> < (\<mu>, \<rho>) , V x > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >"
    proof(rule exI[where x = "\<mu>"],
          rule exI[where x = "\<rho>"],
          rule exI[where x = "Inr (SLoc xl, k)"],
          rule conjI)
      from env_compat show "(\<Gamma> \<union> {(x, f \<tau>)}) \<leftrightarrow> (\<mu>, \<rho>)" by simp
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
    show "\<exists>\<mu>' \<rho>' \<L>'. ((\<Gamma> \<union> {(x, f (empty, t))}) \<leftrightarrow> (\<mu>', \<rho>')) \<and> 
                     < (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>', \<rho>') , \<L>' >"
    proof(rule exI[where x = "\<mu>(x \<mapsto> (l, SLoc l))"],
          rule exI[where x = "\<rho>(l \<mapsto> (t, emptyVal t))"],
          rule exI[where x = "Inr (SLoc l, SLoc l)"],
          rule conjI)
      from env_compat show "(\<Gamma> \<union> {(x, f (empty, t))}) \<leftrightarrow> (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t)))"
        by auto
      from not_in_lookup and has_loc
      show "< (\<mu>, \<rho>) , var x : t > \<rightarrow> < (\<mu>(x \<mapsto> (l, SLoc l)), \<rho>(l \<mapsto> (t, emptyVal t))) , Inr (SLoc l, SLoc l) >"
        by (rule EVarDef)
    qed
  qed
qed

end
