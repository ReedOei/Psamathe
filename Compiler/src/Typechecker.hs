{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Typechecker where

import Control.Lens
import Control.Monad.State

import AST
import Env
import Phase
import Transform

instance ProgramTransform Typechecking Compiling where
    transformXType = transformQuantifiedType

typecheck :: Program Typechecking -> State (Env Compiling) (Program Compiling)
typecheck prog@(Program decls stmts) = do
    checkedDecls <- mapM checkDecl decls
    checkedStmts <- mapM checkStmt stmts
    pure $ Program checkedDecls checkedStmts

checkDecl :: Decl Typechecking -> State (Env Compiling) (Decl Compiling)
checkDecl = transformDecl

checkStmt :: Stmt Typechecking -> State (Env Compiling) (Stmt Compiling)
checkStmt = transformStmt
