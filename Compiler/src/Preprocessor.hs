module Preprocessor where

import Control.Lens (over, set)
import Control.Monad.State (State, modify)

import qualified Data.Map as Map

import AST
import Env
import Error

-- TODO: Probably want to have multiple AST types for better type safety
preprocess :: Program -> State Env Program
preprocess (Program decls stmts) = do
    newProg <- Program <$> (concat <$> mapM preprocessDecl decls)
                       <*> (concat <$> mapM preprocessStmt stmts)
    modify $ set typeEnv Map.empty
    pure newProg

preprocessDecl :: Decl -> State Env [Decl]
preprocessDecl (TransformerDecl name args ret body) = do
    newBody <- concat <$> mapM preprocessStmt body
    modify $ set typeEnv Map.empty
    pure [TransformerDecl name args ret newBody]
preprocessDecl d = pure [d]

-- TODO: Might need to make this more flexible, in case we need to generate declarations or something
preprocessStmt :: Stmt -> State Env [Stmt]
preprocessStmt (OnlyWhen cond) = preprocessCond cond
preprocessStmt s@(Flow _ dst) = do
    declareVars dst
    pure [s]
preprocessStmt s@(FlowTransform _ _ dst) = do
    declareVars dst
    pure [s]
preprocessStmt s = pure [s]

declareVars :: Locator -> State Env ()
declareVars (NewVar x t) = modify $ over typeEnv $ Map.insert x t
declareVars _ = pure ()

preprocessCond :: Precondition -> State Env [Stmt]
preprocessCond (Conj conds) = concat <$> mapM preprocessCond conds
preprocessCond (BinOp op a b) = do
    (allocA, newA) <- allocateVar a
    newAllocA <- concat <$> mapM preprocessStmt allocA
    (allocB, newB) <- allocateVar b
    newAllocB <- concat <$> mapM preprocessStmt allocB
    res <- expandCond $ BinOp op newA newB
    pure $ newAllocA ++ newAllocB ++ res

allocateVar :: Locator -> State Env ([Stmt], Locator)
allocateVar (IntConst n) = do
    x <- freshName
    pure ([ Flow (IntConst n) (NewVar x Nat) ], Var x)
allocateVar (BoolConst b) = do
    x <- freshName
    pure ([ Flow (BoolConst b) (NewVar x PsaBool) ], Var x)
allocateVar l@(Multiset elemT elems) = do
    x <- freshName
    pure ([ Flow l (NewVar x (Table [] elemT))], Var x)
allocateVar l = pure ([], l)

expandCond :: Precondition -> State Env [Stmt]
expandCond (Conj conds) = concat <$> mapM expandCond conds
-- TODO: We need to be able to write things like "x + 1" in locators for this to work out nicely (alternatively, we could compile things like:
-- only when a <= b
-- into
-- b --[ a ]-> var temp : t
-- b --[ 1 ]-> temp
-- temp --> b
-- But that's kind of annoying, and requires type information)
expandCond cond@(BinOp OpLt a b) = do
    addError $ UnimplementedError "only when" $ show cond
    pure []
expandCond cond@(BinOp OpGt a b) = do
    addError $ UnimplementedError "only when" $ show cond
    pure []
expandCond (BinOp OpEq a b) = pure [ Flow (Select a b) a, Flow (Select b a) b ]
expandCond (BinOp OpIn a b) = do
    tyA <- typeOfLoc a
    --- TODO: Once we have type quantity inference, we can replace Any here with something more specific. Regardless, this should always be safe.
    pure [ Flow (Select b (Multiset (Any, tyA) [a])) b ]
expandCond (BinOp OpNe a b) = do
    v <- Var <$> freshName
    failure <- expandCond (BinOp OpEq a b)
    pure [Try (failure ++ [ Revert ]) []]
expandCond cond@(BinOp OpLe a b) = pure [ Flow (Select b a) b ]
expandCond cond@(BinOp OpGe a b) = expandCond (BinOp OpLt b a)

