{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module AST where

import Data.Char (toLower)
import Data.List (intercalate)

data Modifier = Fungible | Immutable | Consumable | Asset | Unique
    deriving (Show, Eq)

data TyQuant = Empty | Any | One | Nonempty
    deriving (Show, Eq)
type Type = (TyQuant, BaseType)
data BaseType = Nat | PsaBool | PsaString | Address
              | Record [String] [VarDef]
              | Table [String] Type
              | Named String
    deriving (Show, Eq)

type VarDef = (String, Type)

data Locator = IntConst Integer
             | BoolConst Bool
             | StrConst String
             | AddrConst String
             | Var String
             | Multiset Type [Locator]
             | NewVar String BaseType
             | Consume
             | RecordLit [String] [(VarDef, Locator)]
             | Filter Locator TyQuant String [Locator]
             | Select Locator Locator
    deriving (Show, Eq)

data Transformer = Call String [Locator]
                 | Construct String [Locator]
    deriving (Show, Eq)

data Stmt = Flow Locator Locator
          | FlowTransform Locator Transformer Locator
          | Try [Stmt] [Stmt]
    deriving (Show, Eq)

data Decl = TypeDecl String [Modifier] BaseType
          | TransformerDecl String [VarDef] VarDef [Stmt]
    deriving (Show, Eq)

data Program = Program [Decl] [Stmt]
    deriving (Show, Eq)

-- Solidity stuff
data DataLoc = Memory | Calldata | Storage
    deriving (Show, Eq)

data SolType = SolTypeName String
             | SolArray SolType
             | SolMapping SolType SolType
    deriving (Show, Eq)

data SolVarDecl = SolVarLocDecl SolType DataLoc String
                | SolVarDecl SolType String
    deriving (Show, Eq)

data SolExpr = SolBool Bool
             | SolInt Integer
             | SolAddr String
             | SolStr String
             | SolVar String
             | FieldAccess SolExpr String
             | SolPostInc SolExpr
             | SolCall SolExpr [SolExpr]
             | SolIdx SolExpr SolExpr
             | SolAdd SolExpr SolExpr
             | SolSub SolExpr SolExpr
             | SolOr SolExpr SolExpr
             | SolLt SolExpr SolExpr
             | SolLte SolExpr SolExpr
             | SolEq SolExpr SolExpr
    deriving (Show, Eq)

data SolStmt = ExprStmt SolExpr
             | SolVarDefInit SolVarDecl SolExpr
             | SolVarDef SolVarDecl
             | SolAssign SolExpr SolExpr
             | Delete SolExpr
             | For SolStmt SolExpr SolExpr [SolStmt]
             | SolTry SolExpr [SolVarDecl] [SolStmt] [SolStmt]
             | If SolExpr [SolStmt]
    deriving (Show, Eq)

data Visibility = Public | Private | Internal | External
    deriving (Show, Eq)

data SolDecl = Struct String [SolVarDecl]
             | Function String [SolVarDecl] Visibility [SolVarDecl] [SolStmt]
             | Constructor [SolVarDecl] [SolStmt]
             | FieldDef SolVarDecl
    deriving (Show, Eq)

data Contract = Contract String String [SolDecl]
    deriving (Show, Eq)

class PrettyPrint a where
    prettyPrint :: a -> [String]

    prettyStr :: a -> String
    prettyStr = intercalate "\n" . prettyPrint

indent = ("    "++)

instance PrettyPrint Locator where
    prettyPrint (IntConst i) = [show i]
    prettyPrint (BoolConst b) = [ map toLower $ show b ]
    prettyPrint (StrConst s) = [ show s ]
    prettyPrint (AddrConst s) = [s]
    prettyPrint (Var x) = [x]
    prettyPrint (Multiset t elems) = [ "[ " ++ prettyStr t ++ " ; " ++ intercalate ", " (map prettyStr elems) ++ " ]" ]
    prettyPrint (NewVar x t) = [ "var " ++ x ++ " : " ++ prettyStr t ]
    prettyPrint Consume = ["consume"]
    prettyPrint (Filter l q f args) = [ prettyStr l ++ "[ " ++ prettyStr q ++ " such that " ++ f ++ "(" ++ intercalate "," (map prettyStr args) ++ ")]" ]
    prettyPrint (Select l k) = [ prettyStr l ++ "[" ++ prettyStr k ++ "]" ]
    prettyPrint (RecordLit keys fields) = [ "record(" ++ intercalate ", " keys ++ ") {" ++ intercalate ", " (map (\(x, t) -> prettyStr x ++ " |-> " ++ prettyStr t) fields) ]

instance PrettyPrint Transformer where
    prettyPrint (Call name args) = [ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ")" ]
    prettyPrint (Construct name args) = [ "new " ++ name ++ "(" ++ intercalate "," (map prettyStr args) ++ ")" ]

instance PrettyPrint Stmt where
    prettyPrint (Flow src dst) = [ prettyStr src ++ " --> " ++ prettyStr dst ]
    prettyPrint (FlowTransform src transformer dst) = [ prettyStr src ++ " --> " ++ prettyStr transformer ++ " --> " ++ prettyStr dst ]
    prettyPrint (Try tryBlock catchBlock) =
        [ "try {" ]
        ++ concatMap (map indent . prettyPrint) tryBlock
        ++ [ "} catch { " ]
        ++ concatMap (map indent . prettyPrint) catchBlock
        ++ [ "}" ]

instance PrettyPrint Modifier where
    prettyPrint Fungible = ["fungible"]
    prettyPrint Asset = ["asset"]
    prettyPrint Immutable = ["immutable"]
    prettyPrint Unique = ["unique"]
    prettyPrint Consumable = ["consumable"]

instance PrettyPrint TyQuant where
    prettyPrint Empty = ["empty"]
    prettyPrint Any = ["any"]
    prettyPrint One = ["one"]
    prettyPrint Nonempty = ["nonempty"]

instance PrettyPrint Type where
    prettyPrint (q,t) = [ prettyStr q ++ " " ++ prettyStr t ]

instance PrettyPrint VarDef where
    prettyPrint (x,t) = [ x ++ " : " ++ prettyStr t ]

instance PrettyPrint BaseType where
    prettyPrint Nat = ["nat"]
    prettyPrint PsaBool = ["bool"]
    prettyPrint PsaString = ["string"]
    prettyPrint Address = ["address"]
    prettyPrint (Named t) = [t]
    prettyPrint (Table keys (q,t)) = [ "table(" ++ intercalate "," keys ++ ") " ++ prettyStr q ++ " " ++ prettyStr t ]
    prettyPrint (Record keys fields) = [ "record(" ++ intercalate "," keys ++ ") {" ++ intercalate ", " (map prettyStr fields) ++ "}" ]

instance PrettyPrint Decl where
    prettyPrint (TypeDecl name ms baseT) =
        [ "type " ++ name ++ " is " ++ intercalate " " (map prettyStr ms) ++ " " ++ prettyStr baseT ]
    prettyPrint (TransformerDecl name args ret body) =
        [ "transformer " ++ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ") -> " ++ prettyStr ret ++ "{"]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]

instance PrettyPrint Program where
    prettyPrint (Program decls mainBody) =
        concatMap prettyPrint decls ++ concatMap prettyPrint mainBody

instance PrettyPrint SolExpr where
    prettyPrint (SolBool b) = [ map toLower $ show b ]
    prettyPrint (SolInt i) = [ show i ]
    prettyPrint (SolStr s) = [ show s ]
    prettyPrint (SolAddr addr)  = [ addr ]
    prettyPrint (SolVar x) = [ x ]
    prettyPrint (FieldAccess e x) = [ prettyStr e ++ "." ++ x ]
    prettyPrint (SolPostInc e) = [ prettyStr e ++ "++" ]
    prettyPrint (SolCall recv args) = [ prettyStr recv ++ "(" ++ intercalate "," (map prettyStr args) ++ ")" ]
    prettyPrint (SolIdx e idxE) = [ prettyStr e ++ "[" ++ prettyStr idxE ++ "]" ]
    prettyPrint (SolAdd e1 e2) = [ "(" ++ prettyStr e1 ++ ") + (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolSub e1 e2) = [ "(" ++ prettyStr e1 ++ ") - (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolOr e1 e2) = [ "(" ++ prettyStr e1 ++ ") || (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolLt e1 e2) = [ "(" ++ prettyStr e1 ++ ") < (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolLte e1 e2) = [ "(" ++ prettyStr e1 ++ ") <= (" ++ prettyStr e2 ++ ")" ]
    prettyPrint (SolEq e1 e2) = [ "(" ++ prettyStr e1 ++ ") == (" ++ prettyStr e2 ++ ")" ]

instance PrettyPrint SolStmt where
    prettyPrint (ExprStmt e) = [prettyStr e ++ ";"]
    prettyPrint (SolVarDefInit decl e) = [ prettyStr decl ++ " = " ++ prettyStr e ++ ";" ]
    prettyPrint (SolVarDef decl) = [ prettyStr decl ++ ";" ]
    prettyPrint (SolAssign e1 e2) = [ prettyStr e1 ++ " = " ++ prettyStr e2 ++ ";" ]
    prettyPrint (Delete e) = ["delete " ++ prettyStr e ++ ";"]
    prettyPrint (For init cond step body) =
        ["for (" ++ prettyStr init ++ " " ++ prettyStr cond ++ "; " ++ prettyStr step ++ ") {"]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]
    prettyPrint (If cond thenBody) =
        ["if (" ++ prettyStr cond ++ ") {"]
        ++ concatMap (map indent . prettyPrint) thenBody
        ++ [ "}" ]
    prettyPrint (SolTry e rets tryBody catchBody) =
        ["try " ++ prettyStr e ++ " returns (" ++ intercalate ", " (map prettyStr rets) ++ ") {"]
        ++ concatMap (map indent . prettyPrint) tryBody
        ++ [ "} catch {" ]
        ++ concatMap (map indent . prettyPrint) catchBody
        ++ [ "}" ]

instance PrettyPrint DataLoc where
    prettyPrint Memory = ["memory"]
    prettyPrint Calldata = ["calldata"]
    prettyPrint Storage = ["storage"]

instance PrettyPrint Visibility where
    prettyPrint Public = ["public"]
    prettyPrint Private = ["private"]
    prettyPrint Internal = ["internal"]
    prettyPrint External = ["external"]

instance PrettyPrint SolType where
    prettyPrint (SolTypeName s) = [ s ]
    prettyPrint (SolArray t) = [ prettyStr t ++ "[]" ]
    prettyPrint (SolMapping k v) = [ "mapping " ++ prettyStr k ++ " => " ++ prettyStr v ]

instance PrettyPrint SolVarDecl where
    prettyPrint (SolVarLocDecl t loc x) = [ prettyStr t ++ " " ++ prettyStr loc ++ " " ++ x ]
    prettyPrint (SolVarDecl t x) = [ prettyStr t ++ " " ++ x ]

instance PrettyPrint SolDecl where
    prettyPrint (Struct name varDecls) =
        [ "struct " ++ name ++ "{" ]
        ++ map (indent . (++";") . prettyStr) varDecls
        ++ [ "}" ]
    prettyPrint (Function name args vis rets body) =
        [ "function " ++ name ++ "(" ++ intercalate ", " (map prettyStr args) ++ ") " ++ prettyStr vis ++ " returns (" ++ intercalate "," (map prettyStr rets) ++ ") {" ]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]
    prettyPrint (Constructor args body) =
        [ "constructor (" ++ intercalate "," (map prettyStr args) ++ ") {" ]
        ++ concatMap (map indent . prettyPrint) body
        ++ [ "}" ]

instance PrettyPrint Contract where
    prettyPrint (Contract ver name decls) =
        [ "pragma soldidity ^" ++ ver ++ ";",
          "contract " ++ name ++ " {" ]
        ++ concatMap (map indent . prettyPrint) decls
        ++ [ "}" ]

