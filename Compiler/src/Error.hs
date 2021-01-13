{-# LANGUAGE DeriveAnyClass #-}

module Error where

import AST

-- Wrapper for PrettyPrint
class (PrettyPrint a) => Error a

-- Various error types
newtype FlowError = FlowError String deriving (Eq, Error)

newtype SyntaxError = SyntaxError String deriving (Eq, Error)

data UnimplementedError = UnimplementedError String String deriving (Eq, Error)

data TypeError = TypeError String BaseType deriving (Eq, Error)

data LookupError = LookupErrorVar String | LookupErrorType String | LookupErrorTypeDecl Decl deriving (Eq, Error)

-- Definitions of prettyPrint for error types
instance PrettyPrint FlowError where
    prettyPrint (FlowError s) = ["FlowError: " ++ s]

instance PrettyPrint SyntaxError where
    prettyPrint (SyntaxError s) = ["SyntaxError: " ++ s]

instance PrettyPrint UnimplementedError where
    prettyPrint (UnimplementedError feature target) = ["UnimplementedError: " ++ feature ++ " is not implemented for " ++ target]

instance PrettyPrint TypeError where
    prettyPrint (TypeError s t) = ["TypeError: " ++ s ++ " type " ++ show t]

instance PrettyPrint LookupError where
    prettyPrint (LookupErrorVar s) = ["LookupError: Variable " ++ s ++ " is not defined"]
    prettyPrint (LookupErrorType s) = ["LookupError: Type " ++ s ++ " is not defined"]
    prettyPrint (LookupErrorTypeDecl (TransformerDecl tx _ _ _)) = ["LookupError: expected type but got transformer" ++ show tx]

-- dummy values that are returned as proxies when errors are encountered
dummyBaseType :: BaseType
dummyBaseType = Bot

dummyDecl :: Decl
dummyDecl = TypeDecl "unknownDecl__" [] dummyBaseType

dummySolExpr :: SolExpr
dummySolExpr = SolVar "unknownExpr__"
