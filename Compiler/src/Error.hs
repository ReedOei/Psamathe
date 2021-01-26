{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Error where

import AST

data Error phase = FlowError String
           | SyntaxError String
           | UnimplementedError String String
           | TypeError String (BaseType phase)
           | FieldNotFoundError String (BaseType phase)
           | LookupError (LookupErrorCat phase)

data LookupErrorCat phase = LookupErrorVar String | LookupErrorType String | LookupErrorTypeDecl (Decl phase)

deriving instance Eq (XType phase) => Eq (Error phase)
deriving instance Eq (XType phase) => Eq (LookupErrorCat phase)

deriving instance Show (XType phase) => Show (Error phase)
deriving instance Show (XType phase) => Show (LookupErrorCat phase)

instance Show (XType phase) => PrettyPrint (Error phase) where
    prettyPrint (FlowError s) = ["FlowError: " ++ s]
    prettyPrint (SyntaxError s) = ["SyntaxError: " ++ s]
    prettyPrint (UnimplementedError feature target) = ["UnimplementedError: " ++ feature ++ " is not implemented for " ++ target]
    prettyPrint (TypeError s t) = ["TypeError: " ++ s ++ " type " ++ show t]
    prettyPrint (FieldNotFoundError x t) = ["FieldNotFoundError: Field " ++ x ++ " not found in type " ++ show t]
    prettyPrint (LookupError (LookupErrorVar s)) = ["LookupError: Variable " ++ s ++ " is not defined"]
    prettyPrint (LookupError (LookupErrorType s)) = ["LookupError: Type " ++ s ++ " is not defined"]
    prettyPrint (LookupError (LookupErrorTypeDecl (TransformerDecl tx _ _ _))) = ["LookupError: expected type but got transformer" ++ show tx]

-- dummy values that are returned as proxies when errors are encountered
dummyBaseType :: BaseType Parsed
dummyBaseType = Bot

dummyType :: QuantifiedType Parsed
dummyType = (Any, Bot)

dummyDecl :: Decl Parsed
dummyDecl = TypeDecl "unknownDecl__" [] dummyBaseType

dummySolExpr :: SolExpr
dummySolExpr = SolVar "unknownExpr__"
