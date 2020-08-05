:qa
theory Psamathe
  imports Main
begin

datatype TyQuant = any | one | nonempty | empty | every
datatype Modifier = fungible | unique | immutable | consumable | asset
datatype BaseType = V string 
  | T string "Modifier set" BaseType
  | Set "TyQuant \<times> BaseType"
  | Func "TyQuant \<times> BaseType" "TyQuant \<times> BaseType"
  | Forall string "TyQuant \<times> BaseType"
datatype Expr = EmptySet 
  | Single Expr
  | Var string
  | Lambda string "TyQuant \<times> BaseType" Expr
  | TyLambda string Expr
  | App Expr Expr
  | TyApp Expr "BaseType"
  | Flow Expr Expr

type_synonym Type = "TyQuant \<times> BaseType"
type_synonym TypeEnv = "string \<Rightarrow> Type"

function demote     :: "Type \<Rightarrow> Type" 
  and    demoteBase :: "BaseType \<Rightarrow> BaseType" where
  "demote (q, t) = (q, demoteBase t)"
| "demoteBase (V x) = (V x)"
| "demoteBase (T _ _ base) = demoteBase base" 
| "demoteBase (Set ty) = Set (demote ty)"
| "demoteBase (Func a b) = Func (demote a) (demote b)"
| "demoteBase (Forall v ty) = Forall v (demote ty)"
  by pat_completeness auto

fun isAsset :: "Type \<Rightarrow> bool" where
  "isAsset (empty, _) = False"
| "isAsset (q, V _) = True" (* Temp *)
| "isAsset (q, T _ mods base) = ((asset \<in> mods) \<or> isAsset (q, base))"
| "isAsset (q, Set elemTy) = isAsset elemTy"
| "isAsset (q, Func _ _) = False"
| "isAsset (q, Forall _ t) = False" (* TODO: Is this right?*)

fun tySubs :: "string \<Rightarrow> BaseType \<Rightarrow> BaseType \<Rightarrow> BaseType" where
  "tySubs y newTy (V x) = (if x = y then newTy else (V x))"
| "tySubs y newTy (T t mods base) = T t mods (tySubs y newTy base)" (* TODO : Is this right? *)
| "tySubs y newTy (Set (q, elemTy)) = Set (q, tySubs y newTy elemTy)"
| "tySubs y newTy (Func (qA, a) (qB, b)) = Func (qA, tySubs y newTy a) (qB, tySubs y newTy b)"
| "tySubs y newTy (Forall v (q, ty)) = Forall v (q, tySubs y newTy ty)"

inductive expr_type :: "TypeEnv \<Rightarrow> Expr \<Rightarrow> Type \<Rightarrow> TypeEnv \<Rightarrow> bool" ("_ \<turnstile> _ : _ \<stileturn> _") where
  DemoteLookup: "expr_type \<Gamma> (Var x) (demote (\<Gamma> x)) \<Gamma>"
| LinLookup: "\<lbrakk> \<Gamma> x = (q, t); demote (\<Gamma> x) \<noteq> \<Gamma> x \<rbrakk> \<Longrightarrow> expr_type \<Gamma> (Var x) (q, t) (\<Gamma> (x := (empty, t)))"
| EmptySet: "expr_type env EmptySet (empty, Set t) env"
| SingletonSet: "\<lbrakk> expr_type \<Gamma> e t \<Delta> \<rbrakk> \<Longrightarrow> expr_type \<Gamma> (Single e) (one, Set t) \<Delta>"
| Abs: "\<lbrakk> expr_type (\<Gamma> (x := ty)) body codom (\<Gamma> (x := final)); 
          \<not>(isAsset final) \<rbrakk> \<Longrightarrow> expr_type \<Gamma> (Lambda x ty body) (one, Func ty codom) \<Gamma>"
| App: "\<lbrakk> expr_type \<Gamma> f (q, Func a b) \<Delta>;
          expr_type \<Delta> e a \<Xi> \<rbrakk> \<Longrightarrow> expr_type \<Gamma> (App f e) b \<Xi>"
| TyAbs: "\<lbrakk> expr_type \<Gamma> body t \<Delta> \<rbrakk> \<Longrightarrow> expr_type \<Gamma> (TyLambda \<alpha> body) (one, Forall \<alpha> t) \<Delta>"
| TyApp: "\<lbrakk> expr_type \<Gamma> f (_, Forall \<alpha> (q, ty)) \<Delta> \<rbrakk> \<Longrightarrow> expr_type \<Gamma> (TyApp f tyArg) (q, tySubs \<alpha> tyArg ty) \<Delta>"

(* TODO: Do flow typing... *)

inductive is_val :: "Expr \<Rightarrow> bool" where
  EmptyVal: "is_val EmptySet"
| SingletonVal: "\<lbrakk> is_val elem \<rbrakk> \<Longrightarrow> is_val (Single elem)"
| LambdaVal: "is_val (Lambda _ _ _)"
| TyLambdaVal: "is_val (TyLambda _ _)"

fun substitute :: "string \<Rightarrow> Expr \<Rightarrow> Expr \<Rightarrow> Expr" where
  "substitute y e EmptySet = EmptySet"
| "substitute y e (Single a) = Single (substitute y e a)"
| "substitute y e (Var x) = (if x = y then e else (Var x))"
| "substitute y e (Lambda x ty body) = Lambda x ty (substitute y e body)"
| "substitute y e (App f arg) = App (substitute y e f) (substitute y e arg)"
| "substitute y e (TyLambda alpha body) = TyLambda alpha (substitute y e body)"
| "substitute y e (TyApp f tyArg) = TyApp (substitute y e f) tyArg"
| "substitute y e (Flow src sel) = Flow (substitute y e src) (substitute y e sel)"

fun tySubsExpr :: "string \<Rightarrow> BaseType \<Rightarrow> Expr \<Rightarrow> Expr" where
  "tySubsExpr alpha ty EmptySet = EmptySet"
| "tySubsExpr alpha ty (Single a) = Single (tySubsExpr alpha ty a)"
| "tySubsExpr alpha ty (Var x) = Var x"
| "tySubsExpr alpha ty (Lambda x (q, argTy) body) = Lambda x (q, tySubs alpha ty argTy) (tySubsExpr alpha ty body)"
| "tySubsExpr alpha ty (App f arg) = App (tySubsExpr alpha ty f) (tySubsExpr alpha ty arg)"
| "tySubsExpr alpha ty (TyLambda beta body) = TyLambda beta (tySubsExpr alpha ty body)"
| "tySubsExpr alpha ty (TyApp f tyArg) = TyApp (tySubsExpr alpha ty f) (tySubs alpha ty tyArg)"
| "tySubsExpr alpha ty (Flow src sel) = Flow (tySubsExpr alpha ty src) (tySubsExpr alpha ty sel)"

inductive eval :: "Expr \<Rightarrow> Expr \<Rightarrow> bool" (infix "\<rightarrow>" 90) where
  CongrSingleton: "\<lbrakk> e1 \<rightarrow> e2 \<rbrakk> \<Longrightarrow> Singleton e1 \<rightarrow> Singleton e2"
| AppCongr: "\<lbrakk> f1 \<rightarrow> f2 \<rbrakk> \<Longrightarrow> App f1 e \<rightarrow> App f2 e"
| BetaRed: "App (Lambda x _ body) arg \<rightarrow> substitute x arg body"
| TyAppCongr: "\<lbrakk> f1 \<rightarrow> f2 \<rbrakk> \<Longrightarrow> TyApp f1 tyArg \<rightarrow> TyApp f2 tyArg"
| TyAppBetaRed: "TyApp (TyLambda alpha body) tyArg \<rightarrow> tySubsExpr alpha tyArg body"
(* | FlowCongr: "\<lbrakk> *)

fun free_vars :: "Expr \<Rightarrow> string list" where
  "free_vars EmptySet = Nil"
| "free_vars (Single a) = free_vars a"
| "free_vars (Var x) = [x]"
| "free_vars (Lambda x _ body) = filter (\<lambda>y. x \<noteq> y) (free_vars body)"
| "free_vars (App f arg) = (free_vars f @ free_vars arg)"
| "free_vars (TyLambda _ body) = free_vars body"
| "free_vars (TyApp f _) = free_vars f"
| "free_vars (Flow src sel) = free_vars src @ free_vars sel"

definition closed :: "Expr \<Rightarrow> bool" where "closed x = (free_vars x = [])"
declare closed_def[simp]

lemma closed_single[simp]: "closed e \<longleftrightarrow> closed (Single e)"
  by simp

thm eval.cases
thm expr_type.induct

theorem progress: "\<lbrakk> closed e; \<Gamma> \<turnstile> e : t \<stileturn> \<Delta> \<rbrakk> \<Longrightarrow> is_val e \<or> (\<exists>e'. e \<rightarrow> e')"
  (*  e :: Expr and gamma :: TypeEnv and t :: Type and delta :: TypeEnv
  assumes closed: "closed e"
  assumes well_typed: "expr_type gamma e t delta"
  shows "is_val e \<or> (\<exists>e'. e \<rightarrow> e')"
  using closed and well_typed *)
proof(induct e arbitrary: \<Gamma> t \<Delta>)
  case EmptySet then show ?case
    apply clarsimp
    apply (rule EmptyVal)
    done
next
  case (Single e)
  have "closed (Single e)" using this by auto
  have "closed e" sorry
  have "is_val e \<or> (\<exists>e'. e \<rightarrow> e')" sorry
  then show ?case
    apply clarsimp
    apply (rule SingletonVal)
    apply (frule expr_type.cases)
    apply auto
next
  case (Var x)
  then show ?case sorry
next
  case (Lambda x1 x2a x3a)
  then show ?case sorry
next
  case (TyLambda x1 x2a)
  then show ?case sorry
next
  case (App x1 x2a)
  then show ?case sorry
next
  case (TyApp x1 x2a)
  then show ?case sorry
next
  case (Flow x1 x2a)
  then show ?case sorry
qed

end
