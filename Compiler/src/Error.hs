{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Error where

import Data.List

import AST
import Phase

data Error phase = FlowError String
                 | SyntaxError String
                 | UnimplementedError String String
                 | TypeError String (BaseType phase)
                 | FieldNotFoundError String (BaseType phase)
                 | LookupError (LookupErrorCat phase)

data LookupErrorCat phase = LookupErrorVar String | LookupErrorType String | LookupErrorTypeDecl (Decl phase)

type ErrorPreprocessing = Either (Error Preprocessing) (Error Typechecking)
type ErrorTypechecking = Either (Error Typechecking) (Error Compiling)
type ErrorCompiling = Error Compiling

data ErrorCat = PreprocessorError ErrorPreprocessing
              | TypecheckerError ErrorTypechecking
              | CompilerError ErrorCompiling
    deriving (Show, Eq)

class Errorable e where
    toErrorCat :: e -> PhaseMarker -> ErrorCat

instance Errorable (Error Preprocessing) where
    toErrorCat e Preprocessor = PreprocessorError $ Left e

instance Errorable (Error Typechecking) where
    toErrorCat e Preprocessor = PreprocessorError $ Right e
    toErrorCat e Typechecker = TypecheckerError $ Left e

instance Errorable (Error Compiling) where
    toErrorCat e Typechecker = TypecheckerError $ Right e
    toErrorCat e Compiler = CompilerError e

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

groupErrors :: [ErrorCat] -> ([ErrorPreprocessing], [ErrorTypechecking], [ErrorCompiling])
groupErrors = mconcat . map groupError
    where
        groupError (PreprocessorError e) = ([e], [], [])
        groupError (TypecheckerError e) = ([], [e], [])
        groupError (CompilerError e) = ([], [], [e])

indentString :: String -> String
indentString = unlines . map indent . lines

instance PrettyPrint ErrorPreprocessing where
    prettyPrint (Left e) = prettyPrint e
    prettyPrint (Right e) = prettyPrint e

instance PrettyPrint ErrorTypechecking where
    prettyPrint (Left e) = prettyPrint e
    prettyPrint (Right e) = prettyPrint e

instance PrettyPrint [ErrorCat] where
    prettyPrint errors = concat [
            printError "Preprocessor errors" preprocessorErrors,
            printError "Typechecker errors" typecheckerErrors,
            printError "Compiler errors" compilerErrors
        ]
        where
            (preprocessorErrors, typecheckerErrors, compilerErrors) = groupErrors errors
            printError phase errors  = if (not . null) errors then phase : map indent (concatMap prettyPrint errors) else []
