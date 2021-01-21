module Error where

import AST

data Error = FlowError String
           | SyntaxError String
           | UnimplementedError String String
           | TypeError String BaseType
           | FieldNotFoundError String BaseType
           | LookupError LookupErrorCat
    deriving (Show, Eq)

data LookupErrorCat = LookupErrorVar String | LookupErrorType String | LookupErrorTypeDecl Decl
    deriving (Eq, Show)

instance PrettyPrint Error where
    prettyPrint (FlowError s) = ["FlowError: " ++ s]
    prettyPrint (SyntaxError s) = ["SyntaxError: " ++ s]
    prettyPrint (UnimplementedError feature target) = ["UnimplementedError: " ++ feature ++ " is not implemented for " ++ target]
    prettyPrint (TypeError s t) = ["TypeError: " ++ s ++ " type " ++ show t]
    prettyPrint (FieldNotFoundError x t) = ["FieldNotFoundError: Field " ++ x ++ " not found in type " ++ show t]
    prettyPrint (LookupError (LookupErrorVar s)) = ["LookupError: Variable " ++ s ++ " is not defined"]
    prettyPrint (LookupError (LookupErrorType s)) = ["LookupError: Type " ++ s ++ " is not defined"]
    prettyPrint (LookupError (LookupErrorTypeDecl (TransformerDecl tx _ _ _))) = ["LookupError: expected type but got transformer" ++ show tx]

-- dummy values that are returned as proxies when errors are encountered
dummyBaseType :: BaseType
dummyBaseType = Bot

dummyType :: Type
dummyType = (Any, Bot)

dummyDecl :: Decl
dummyDecl = TypeDecl "unknownDecl__" [] dummyBaseType

dummySolExpr :: SolExpr
dummySolExpr = SolVar "unknownExpr__"
