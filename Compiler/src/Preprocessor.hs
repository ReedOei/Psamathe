module Preprocessor where

import Control.Monad.State

import AST
import Env

-- TODO: Probably want to have multiple AST types for better type safety
preprocess :: Program -> State Env Program
preprocess (Program decls stmts) =
    Program <$> (concat <$> mapM preprocessDecl decls)
            <*> (concat <$> mapM preprocessStmt stmts)

preprocessDecl :: Decl -> State Env [Decl]
preprocessDecl d = pure [d]

-- TODO: Might need to make this more flexible, in case we need to generate declarations or something
preprocessStmt :: Stmt -> State Env [Stmt]
preprocessStmt s = pure [s]

