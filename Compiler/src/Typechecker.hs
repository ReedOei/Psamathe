module Typechecker where

import Control.Lens
import Control.Monad.State

import AST
import Env

-- TODO: Probably want to have multiple AST types for better type safety
typecheck :: Program -> State Env Program
typecheck prog@(Program decls stmts) = do
    -- NOTE: May need to transform program
    mapM_ checkDecl decls
    mapM_ checkStmt stmts
    pure prog

checkDecl :: Decl -> State Env ()
checkDecl d = pure ()

checkStmt :: Stmt -> State Env ()
checkStmt s = pure ()

