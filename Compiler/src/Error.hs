{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

data ErrorCat = PreprocessorError (Error Parsed)
              | TypecheckerError (Error Preprocessed)
              | CompilerError (Error Typechecked)
    deriving (Eq, Show)

class Errorable e where
    toErrorCat :: e -> ErrorCat

instance Errorable (Error Parsed) where
    toErrorCat e = PreprocessorError e

instance Errorable (Error Preprocessed) where
    toErrorCat e = TypecheckerError e

instance Errorable (Error Typechecked) where
    toErrorCat e = CompilerError e

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
