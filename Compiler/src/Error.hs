module Error where

import AST

data Error = FlowError String
           | SyntaxError String
           | UnimplementedError String String
           | TypeError String BaseType
           | AssetDropError Type
           | LookupError LookupErrorCat
    deriving (Show, Eq)

data LookupErrorCat = LookupErrorVar String | LookupErrorType String | LookupErrorTypeDecl Decl
    deriving (Eq, Show)

instance PrettyPrint Error where
    prettyPrint (FlowError s) = ["FlowError: " ++ s]
    prettyPrint (SyntaxError s) = ["SyntaxError: " ++ s]
    prettyPrint (UnimplementedError feature target) = ["UnimplementedError: " ++ feature ++ " is not implemented for " ++ target]
    prettyPrint (TypeError s t) = ["TypeError: " ++ s ++ " type " ++ show t]
    prettyPrint (AssetDropError ty) = ["AssetDropError: Cannot drop a value of type " ++ show ty ++ " because it is an asset!"]
    prettyPrint (LookupError (LookupErrorVar s)) = ["LookupError: Variable " ++ s ++ " is not defined"]
    prettyPrint (LookupError (LookupErrorType s)) = ["LookupError: Type " ++ s ++ " is not defined"]
    prettyPrint (LookupError (LookupErrorTypeDecl (TransformerDecl tx _ _ _))) = ["LookupError: expected type but got transformer" ++ show tx]

-- dummy values that are returned as proxies when errors are encountered
dummyBaseType :: BaseType
dummyBaseType = Bot

dummyDecl :: Decl
dummyDecl = TypeDecl "unknownDecl__" [] dummyBaseType

dummySolExpr :: SolExpr
dummySolExpr = SolVar "unknownExpr__"
