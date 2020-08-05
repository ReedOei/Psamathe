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

inductive expr_type :: "TypeEnv \<Rightarrow> Expr \<Rightarrow> Type \<Rightarrow> TypeEnv \<Rightarrow> bool" where
  DemoteLookup: "expr_type env (Var x) (demote (env x)) env"
| LinLookup: "\<lbrakk> env x = (q, t); demote (env x) \<noteq> env x \<rbrakk> \<Longrightarrow> expr_type env (Var x) (q, t) (env (x := (empty, t)))"
| EmptySet: "expr_type env EmptySet (empty, Set t) env"
| SingletonSet: "\<lbrakk> expr_type gamma e t delta \<rbrakk> \<Longrightarrow> expr_type gamma (Single e) (one, Set t) delta"
| Abs: "\<lbrakk> expr_type (gamma (x := ty)) body codom (gamma (x := final)); 
          \<not>(isAsset final) \<rbrakk> \<Longrightarrow> expr_type gamma (Lambda x ty body) (one, Func ty codom) gamma"
| App: "\<lbrakk> expr_type gamma f (q, Func a b) delta;
          expr_type delta e a xi \<rbrakk> \<Longrightarrow> expr_type gamma (App f e) b xi"
| TyAbs: "\<lbrakk> expr_type gamma body t delta \<rbrakk> \<Longrightarrow> expr_type gamma (TyLambda alpha body) (one, Forall alpha t) delta"
| TyApp: "\<lbrakk> expr_type gamma f (_, Forall alpha (q, ty)) delta \<rbrakk> \<Longrightarrow> expr_type gamma (TyApp f tyArg) (q, tySubs alpha tyArg ty) delta"

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
| FlowCongr: "\<lbrakk> 

end
