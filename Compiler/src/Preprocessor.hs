{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Preprocessor where

import Control.Lens (over, set)
import Control.Monad.State (State, modify)

import qualified Data.Map as Map

import AST
import Env
import Error
import Phase
import Transform

inferQuant :: (Phase a, Phase b, PhaseTransition a b) => BaseType a -> State (Env b) TyQuant
inferQuant baseT = do
    tIsFungible <- isFungible baseT
    if tIsFungible then
        pure Any
    else
        pure One

instance ProgramTransform Preprocessing Typechecking where
    transformXType (Complete qt) = transformQuantifiedType qt
    transformXType (Infer baseT) = do
        transformedBaseT <- transformBaseType baseT
        tq <- inferQuant baseT
        pure (tq, transformedBaseT)

preprocess :: Program Preprocessing -> State (Env Typechecking) (Program Typechecking)
preprocess (Program decls stmts) = do
    mapM_ defineType decls
    newProg <- Program <$> (concat <$> mapM preprocessDecl decls)
                       <*> (concat <$> mapM preprocessStmt stmts)
    modify $ set typeEnv Map.empty
    pure newProg

defineType :: Decl Preprocessing -> State (Env Typechecking) ()
defineType decl@(TypeDecl name _ _) = do
    transformedDecl <- transformDecl decl
    modify $ over declarations $ Map.insert name transformedDecl

defineType _ = pure ()

preprocessDecl :: Decl Preprocessing -> State (Env Typechecking) [Decl Typechecking]
preprocessDecl (TransformerDecl name args ret body) = do
    newBody <- concat <$> mapM preprocessStmt body
    modify $ set typeEnv Map.empty
    transformedArgs <- mapM transformVarDef args
    transformedRet <- transformVarDef ret
    pure [TransformerDecl name transformedArgs transformedRet newBody]

preprocessDecl d = do
    transformedDecl <- transformDecl d
    pure [transformedDecl]

-- TODO: Might need to make this more flexible, in case we need to generate declarations or something
preprocessStmt :: Stmt Preprocessing -> State (Env Typechecking) [Stmt Typechecking]
preprocessStmt (OnlyWhen cond) = preprocessCond cond
preprocessStmt s@(Flow _ dst) = do
    declareVars dst
    transformedStmt <- transformStmt s
    pure [transformedStmt]

preprocessStmt s@(FlowTransform _ _ dst) = do
    declareVars dst
    transformedStmt <- transformStmt s
    pure [transformedStmt]

preprocessStmt s = do
    transformedStmt <- transformStmt s
    pure [transformedStmt]

declareVars :: Locator Preprocessing -> State (Env Typechecking) ()
declareVars (NewVar x baseT) = do
    transformedBaseT <- transformBaseType baseT
    modify $ over typeEnv $ Map.insert x transformedBaseT

declareVars _ = pure ()

preprocessCond :: Precondition Preprocessing -> State (Env Typechecking) [Stmt Typechecking]
preprocessCond (Conj conds) = concat <$> mapM preprocessCond conds
preprocessCond (Disj []) = pure []
preprocessCond (Disj [cond]) = preprocessCond cond
preprocessCond (Disj (c1:cs)) = do
    checkC1 <- preprocessCond c1
    checkCs <- preprocessCond $ Disj cs
    pure [ Try checkC1 checkCs ]

preprocessCond (NegateCond cond) = preprocessCond $ expandNegate cond

preprocessCond (BinOp op a b) = do
    (allocA, newA) <- allocateVar a
    newAllocA <- concat <$> mapM preprocessStmt allocA
    (allocB, newB) <- allocateVar b
    newAllocB <- concat <$> mapM preprocessStmt allocB
    res <- expandCond $ BinOp op newA newB
    pure $ newAllocA ++ newAllocB ++ res

expandNegate :: Precondition Preprocessing -> Precondition Preprocessing
expandNegate (BinOp OpEq a b) = BinOp OpNe a b
expandNegate (BinOp OpNe a b) = BinOp OpEq a b
expandNegate (BinOp OpLt a b) = BinOp OpGe a b
expandNegate (BinOp OpGt a b) = BinOp OpLe a b
expandNegate (BinOp OpLe a b) = BinOp OpGt a b
expandNegate (BinOp OpGe a b) = BinOp OpLt a b
expandNegate (BinOp OpIn a b) = BinOp OpNotIn a b
expandNegate (BinOp OpNotIn a b) = BinOp OpIn a b
expandNegate (Conj conds) = Disj $ map expandNegate conds

expandNegate (Disj conds) = Conj $ map expandNegate conds

expandNegate (NegateCond cond) = cond

allocateVar :: Locator Preprocessing -> State (Env Typechecking) ([Stmt Preprocessing], Locator Preprocessing)
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

expandCond :: Precondition Preprocessing -> State (Env Typechecking) [Stmt Typechecking]
-- TODO: We need to be able to write things like "x + 1" in locators for this to work out nicely (alternatively, we could compile things like:
-- only when a <= b
-- into
-- b --[ a ]-> var temp : t
-- b --[ 1 ]-> temp
-- temp --> b
-- But that's kind of annoying, and requires type information)
expandCond cond@(BinOp OpLt a b) = do
    addError $ UnimplementedError @Preprocessing "only when" $ show cond
    pure []

expandCond cond@(BinOp OpGt a b) = do
    addError $ UnimplementedError @Preprocessing "only when" $ show cond
    pure []

expandCond (BinOp OpEq a b) = do
    transformedA <- transformLocator a
    transformedB <- transformLocator b
    pure [ Flow (Select transformedA transformedB) transformedA,
           Flow (Select transformedB transformedA) transformedB ]

expandCond (BinOp OpIn a b) = do
    transformedA <- transformLocator a
    transformedB <- transformLocator b
    tyA <- typeOfLoc transformedA
    quant <- inferQuant tyA
    pure [ Flow (Select transformedB (Multiset (quant, tyA) [transformedA])) transformedB ]

expandCond (BinOp OpNe a b) = do
    failure <- expandCond (BinOp OpEq a b)
    pure [Try (failure ++ [ Revert ]) []]

expandCond (BinOp OpLe a b) = do
    transformedA <- transformLocator a
    transformedB <- transformLocator b
    pure [ Flow (Select transformedB transformedA) transformedB ]

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

