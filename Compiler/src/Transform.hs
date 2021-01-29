{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Transform where

import Control.Monad.State

import AST
import Env

-- AST transforms
class ProgramTransform a b where
    transformXType :: XType a -> State (Env b) (XType b)

transformBaseType :: forall a b. ProgramTransform a b => BaseType a -> State (Env b) (BaseType b)
transformBaseType Nat = pure Nat
transformBaseType PsaBool = pure PsaBool
transformBaseType PsaString = pure PsaString
transformBaseType Address = pure Address
transformBaseType (Named name) = pure $ Named name
transformBaseType Bot = pure Bot

transformBaseType (Record keys fields) = do
    transformedFields <- mapM transformVarDef fields
    pure $ Record keys transformedFields

transformBaseType (Table keys t) = do
    transformedT <- transformXType @a @b t
    pure $ Table keys transformedT

transformQuantifiedType :: forall a b. ProgramTransform a b => QuantifiedType a -> State (Env b) (QuantifiedType b)
transformQuantifiedType (q, t) = do
    transformedT <- transformBaseType t
    pure (q, transformedT)

transformVarDef :: forall a b. ProgramTransform a b => VarDef a -> State (Env b) (VarDef b)
transformVarDef (VarDef name t) = do
    transformedT <- transformXType @a @b t
    pure $ VarDef name transformedT

transformLocator :: forall a b. ProgramTransform a b => Locator a -> State (Env b) (Locator b)
transformLocator (IntConst i) = pure $ IntConst i
transformLocator (StrConst s) = pure $ StrConst s
transformLocator (AddrConst addr) = pure $ AddrConst addr
transformLocator (Var var) = pure $ Var var
transformLocator (Field l name) = do
    transformedL <- transformLocator l
    pure $ Field transformedL name

transformLocator (Multiset t locators) = do
    transformedT <- transformXType @a @b t
    transformedLocators <- mapM transformLocator locators

    pure $ Multiset transformedT transformedLocators
transformLocator (NewVar name baseT) = do
    transformedBaseT <- transformBaseType baseT
    pure $ NewVar name transformedBaseT

transformLocator (Filter l q predName args) = do
    transformedL <- transformLocator l
    transformedArgs <- mapM transformLocator args
    pure $ Filter transformedL q predName transformedArgs

transformLocator (Select l k) = do
    transformedL <- transformLocator l
    transformedK <- transformLocator k
    pure $ Select transformedL transformedK

transformTransformer :: ProgramTransform a b => Transformer a -> State (Env b) (Transformer b)
transformTransformer (Construct name args) = do
    transformedArgs <- mapM transformLocator args
    pure $ Construct name transformedArgs

transformTransformer (Call name args) = do
    transformedArgs <- mapM transformLocator args
    pure $ Call name transformedArgs

transformPrecondition :: ProgramTransform a b => Precondition a -> State (Env b) (Precondition b)
transformPrecondition (Conj conds) = do
    transformedConds <- mapM transformPrecondition conds
    pure $ Conj transformedConds

transformPrecondition (Disj conds) = do
    transformedConds <- mapM transformPrecondition conds
    pure $ Disj transformedConds

transformPrecondition (BinOp op a b) = do
    transformedA <- transformLocator a
    transformedB <- transformLocator b
    pure $ BinOp op transformedA transformedB

transformPrecondition (NegateCond cond) = do
    transformedCond <- transformPrecondition cond
    pure $ NegateCond transformedCond

transformStmt :: ProgramTransform a b => Stmt a -> State (Env b) (Stmt b)
transformStmt (Flow src dst) = do
    transformedSrc <- transformLocator src
    transformedDst <- transformLocator dst
    pure $ Flow transformedSrc transformedDst

transformStmt (FlowTransform src transformer dst) = do
    transformedSrc <- transformLocator src
    transformedDst <- transformLocator dst
    transformedTransformer <- transformTransformer transformer
    pure $ FlowTransform transformedSrc transformedTransformer transformedDst

transformStmt (OnlyWhen precondition) = do
    transformedPrecondition <- transformPrecondition precondition
    pure $ OnlyWhen transformedPrecondition

transformStmt (Try checkC1 checkCs) = do
    transformedC1 <- mapM transformStmt checkC1
    transformedCs <- mapM transformStmt checkCs
    pure $ Try transformedC1 transformedCs

transformStmt Revert = pure Revert

transformDecl :: ProgramTransform a b => Decl a -> State (Env b) (Decl b)
transformDecl (TypeDecl s modifiers baseT) = do
    transformedBaseT <- transformBaseType baseT
    pure $ TypeDecl s modifiers transformedBaseT

transformDecl (TransformerDecl name args ret body) = do
    transformedArgs <- mapM transformVarDef args
    transformedRet <- transformVarDef ret
    transformedBody <- mapM transformStmt body
    pure $ TransformerDecl name transformedArgs transformedRet transformedBody
