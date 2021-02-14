{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Transform where

import Control.Lens
import Control.Monad.State

import AST
import Env
import Phase

-- | Applies functions accross to (result, Env) pairs across phases
(>>>) :: (ProgramTransform p1 p2, PhaseTransition p1 p1) => (a, Env p1) -> (a -> State (Env p2) b) -> (b, Env p2)
(a, s) >>> f = runState (f a) (transformEnv s)

-- AST transforms
class (Phase a, Phase b) => ProgramTransform a b where
    transformXType :: (Phase c, PhaseTransition a c) => XType a -> State (Env c) (XType b)

transformBaseType :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => BaseType a -> State (Env c) (BaseType b)
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
    transformedT <- transformXType @a @b @c t
    pure $ Table keys transformedT

transformQuantifiedType :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => QuantifiedType a -> State (Env c) (QuantifiedType b)
transformQuantifiedType (q, t) = do
    transformedT <- transformBaseType t
    pure (q, transformedT)

transformVarDef :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => VarDef a -> State (Env c) (VarDef b)
transformVarDef (VarDef name t) = do
    transformedT <- transformXType @a @b t
    pure $ VarDef name transformedT

transformLocator :: forall a b c. (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Locator a -> State (Env c) (Locator b)
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

transformLocator Consume = pure Consume

transformLocator (RecordLit keys members) = do
    let (varDefs, locators) = unzip members
    transformedVarDefs <- mapM transformVarDef varDefs
    transformedLocators <- mapM transformLocator locators
    pure $ RecordLit keys (zip transformedVarDefs transformedLocators)

transformLocator (Filter l q predName args) = do
    transformedL <- transformLocator l
    transformedArgs <- mapM transformLocator args
    pure $ Filter transformedL q predName transformedArgs

transformLocator (Select l k) = do
    transformedL <- transformLocator l
    transformedK <- transformLocator k
    pure $ Select transformedL transformedK

transformTransformer :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Transformer a -> State (Env c) (Transformer b)
transformTransformer (Construct name args) = do
    transformedArgs <- mapM transformLocator args
    pure $ Construct name transformedArgs

transformTransformer (Call name args) = do
    transformedArgs <- mapM transformLocator args
    pure $ Call name transformedArgs

transformPrecondition :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Precondition a -> State (Env c) (Precondition b)
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

transformStmt :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Stmt a -> State (Env c) (Stmt b)
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

transformDecl :: (Phase a, Phase b, Phase c, ProgramTransform a b, PhaseTransition a c) => Decl a -> State (Env c) (Decl b)
transformDecl (TypeDecl s modifiers baseT) = do
    transformedBaseT <- transformBaseType baseT
    pure $ TypeDecl s modifiers transformedBaseT

transformDecl (TransformerDecl name args ret body) = do
    transformedArgs <- mapM transformVarDef args
    transformedRet <- transformVarDef ret
    transformedBody <- mapM transformStmt body
    pure $ TransformerDecl name transformedArgs transformedRet transformedBody

transformEnv :: forall a b. (Phase a, Phase b, ProgramTransform a b, PhaseTransition a a) => Env a -> Env b
transformEnv env = let (transformedTypeEnvs, s) = runState (mapM transformBaseType (view typeEnv env)) env
                       (transformedDecls, _) = runState (mapM transformDecl (view declarations env)) env
                   in Env { _freshCounter = env ^. freshCounter,
                            _typeEnv = transformedTypeEnvs,
                            _declarations = transformedDecls,
                            _solDecls = env ^. solDecls,
                            _allocators = env ^. allocators,
                            _errors = env ^. errors }
