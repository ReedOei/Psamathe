module Preprocessor where

import Control.Monad.State

import AST
import Env
import Error

-- TODO: Probably want to have multiple AST types for better type safety
preprocess :: Program -> State Env Program
preprocess (Program decls stmts) =
    Program <$> (concat <$> mapM preprocessDecl decls)
            <*> (concat <$> mapM preprocessStmt stmts)

preprocessDecl :: Decl -> State Env [Decl]
preprocessDecl d = pure [d]

-- TODO: Might need to make this more flexible, in case we need to generate declarations or something
preprocessStmt :: Stmt -> State Env [Stmt]
preprocessStmt (OnlyWhen cond) = preprocessCond cond
preprocessStmt s = pure [s]

-- TODO: We need to ensure that these conditions are all valid. E.g., something like
-- only when 1 < 2
-- technically makes sense, but gets compiled to
-- 2 --[ 1 ]-> 2
-- which is invalid (2 is not a valid destination)
preprocessCond :: Precondition -> State Env [Stmt]
preprocessCond (Conj conds) = concat <$> mapM preprocessCond conds
preprocessCond (BinOp OpLt a b) = pure [ Flow (Select b a) b ]
preprocessCond (BinOp OpGt a b) = preprocessCond (BinOp OpLt b a)
preprocessCond (BinOp OpEq a b) = pure [ Flow (Select a b) a, Flow (Select b a) b ]
-- NOTE: This is implemented the same as OpLt, but exists
--       basically in case people aren't comfortable considering
--       multiset ordering as a kind of less-than...which I guess is likely
preprocessCond (BinOp OpIn a b) = pure [ Flow (Select b a) b ]
preprocessCond (BinOp OpNe a b) = do
    v <- Var <$> freshName
    failure <- preprocessCond (BinOp OpEq a b)
    pure [Try (failure ++ [ Revert ]) []]
-- TODO: We need to be able to write things like "x + 1" in locators for this to work out nicely (alternatively, we could compile things like:
-- only when a <= b
-- into
-- b --[ a ]-> var temp : t
-- b --[ 1 ]-> temp
-- temp --> b
-- But that's kind of annoying
preprocessCond cond@(BinOp OpLe a b) = do
    addError $ UnimplementedError "only when" $ show cond
    pure []
preprocessCond cond@(BinOp OpGe a b) = do
    addError $ UnimplementedError "only when" $ show cond
    pure []

