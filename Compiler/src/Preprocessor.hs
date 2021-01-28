{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Preprocessor where

import Control.Lens (over, set)
import Control.Monad.State (State, modify)

import qualified Data.Map as Map

import AST
import Env
import Error

instance ProgramTransform Parsed Preprocessed where
    transformXType (Complete qt) = transformQuantifiedType qt
 -- TODO: Proper type quantity inference (placeholder for now)
    transformXType (Infer baseT) = (Any, transformBaseType baseT)

preprocess :: Program Parsed -> State Env (Program Preprocessed)
preprocess (Program decls stmts) = do
    newProg <- Program <$> (concat <$> mapM preprocessDecl decls)
                       <*> (concat <$> mapM preprocessStmt stmts)
    modify $ set typeEnv Map.empty
    pure newProg

preprocessDecl :: Decl Parsed-> State Env [Decl Preprocessed]
preprocessDecl (TransformerDecl name args ret body) = do
    newBody <- concat <$> mapM preprocessStmt body
    modify $ set typeEnv Map.empty
    pure [TransformerDecl name (map transformVarDef args) (transformVarDef ret) newBody]
preprocessDecl d = pure [transformDecl d]

-- TODO: Might need to make this more flexible, in case we need to generate declarations or something
preprocessStmt :: Stmt Parsed -> State Env [Stmt Preprocessed]
preprocessStmt (OnlyWhen cond) = preprocessCond cond
preprocessStmt s@(Flow _ dst) = do
    declareVars dst
    pure [transformStmt s]
preprocessStmt s@(FlowTransform _ _ dst) = do
    declareVars dst
    pure [transformStmt s]
preprocessStmt s = pure [transformStmt s]

declareVars :: Locator Parsed -> State Env ()
declareVars (NewVar x t) = modify $ over typeEnv $ Map.insert x (transformBaseType t)
declareVars _ = pure ()

preprocessCond :: Precondition Parsed -> State Env [Stmt Preprocessed]
preprocessCond (Conj conds) = concat <$> mapM preprocessCond conds
preprocessCond (Disj []) = pure []
preprocessCond (Disj [cond]) = preprocessCond cond
preprocessCond (Disj (c1:cs)) = do
    checkC1 <- preprocessCond c1
    checkCs <- preprocessCond $ Disj cs
    pure [ Try checkC1 checkCs ]
preprocessCond (NegateCond cond) = preprocessCond $ transformPrecondition (expandNegate cond)
preprocessCond (BinOp op a b) = do
    (allocA, newA) <- allocateVar a
    newAllocA <- concat <$> mapM preprocessStmt allocA
    (allocB, newB) <- allocateVar b
    newAllocB <- concat <$> mapM preprocessStmt allocB
    res <- expandCond $ BinOp op newA newB
    pure $ newAllocA ++ newAllocB ++ res

expandNegate :: Precondition Parsed -> Precondition Preprocessed
expandNegate (BinOp OpEq a b) = transformPrecondition (BinOp OpNe a b)
expandNegate (BinOp OpNe a b) = transformPrecondition (BinOp OpEq a b)
expandNegate (BinOp OpLt a b) = transformPrecondition (BinOp OpGe a b)
expandNegate (BinOp OpGt a b) = transformPrecondition (BinOp OpLe a b)
expandNegate (BinOp OpLe a b) = transformPrecondition (BinOp OpGt a b)
expandNegate (BinOp OpGe a b) = transformPrecondition (BinOp OpLt a b)
expandNegate (BinOp OpIn a b) = transformPrecondition (BinOp OpNotIn a b)
expandNegate (BinOp OpNotIn a b) = transformPrecondition (BinOp OpIn a b)
expandNegate (Conj conds) = Disj $ map expandNegate conds
expandNegate (Disj conds) = Conj $ map expandNegate conds
expandNegate (NegateCond cond) = transformPrecondition cond

allocateVar :: Locator Parsed -> State Env ([Stmt Parsed], Locator Parsed)
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

expandCond :: Precondition Parsed -> State Env [Stmt Preprocessed]
-- TODO: We need to be able to write things like "x + 1" in locators for this to work out nicely (alternatively, we could compile things like:
-- only when a <= b
-- into
-- b --[ a ]-> var temp : t
-- b --[ 1 ]-> temp
-- temp --> b
-- But that's kind of annoying, and requires type information)
expandCond cond@(BinOp OpLt a b) = do
    addPreprocessorError $ UnimplementedError "only when" $ show cond
    pure []
expandCond cond@(BinOp OpGt a b) = do
    addPreprocessorError $ UnimplementedError "only when" $ show cond
    pure []
expandCond (BinOp OpEq a b) = pure [
                                Flow (Select (transformLocator a) (transformLocator b)) (transformLocator a),
                                Flow (Select (transformLocator b) (transformLocator a)) (transformLocator b)
                            ]
expandCond (BinOp OpIn a b) = do
    tyA <- typeOfLoc a
    --- TODO: Once we have type quantity inference, we can replace Any here with something more specific. Regardless, this should always be safe.
    pure [ Flow (Select (transformLocator b) (Multiset (Any, tyA) [transformLocator a])) (transformLocator b) ]
expandCond (BinOp OpNe a b) = do
    failure <- expandCond (BinOp OpEq a b)
    pure [Try (failure ++ [ Revert ]) []]
expandCond (BinOp OpLe a b) = pure [ Flow (Select (transformLocator b) (transformLocator a)) (transformLocator b) ]
expandCond (BinOp OpGe a b) = expandCond (BinOp OpLt b a)
expandCond (BinOp OpNotIn a b) = do
    failure <- expandCond (BinOp OpIn a b)
    pure [Try (failure ++ [ Revert ]) []]

-- NOTE: These two should never actually be called
expandCond (Conj conds) = concat <$> mapM expandCond conds
expandCond (Disj (c1:cs)) = do
    checkC1 <- expandCond c1
    checkCs <- expandCond $ Disj cs
    pure [ Try checkC1 checkCs ]

