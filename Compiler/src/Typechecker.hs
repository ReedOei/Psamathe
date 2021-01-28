{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Typechecker where

import Control.Lens
import Control.Monad.State

import AST
import Env

instance ProgramTransform Preprocessed Typechecked where
    transformXType = transformQuantifiedType

typecheck :: Program Preprocessed -> State Env (Program Typechecked)
typecheck prog@(Program decls stmts) = do
    checkedDecls <- mapM checkDecl decls
    checkedStmts <- mapM checkStmt stmts
    pure $ Program checkedDecls checkedStmts

checkDecl :: Decl Preprocessed -> State Env (Decl Typechecked)
checkDecl decl = pure $ transformDecl decl

checkStmt :: Stmt Preprocessed -> State Env (Stmt Typechecked)
checkStmt (Flow src dst) = pure $ Flow (transformLocator src) (transformLocator dst)
