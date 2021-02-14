{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Env where

import Control.Lens (makeLenses, over, (<<+=), view)
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import AST
import Error
import Phase

data Env phase = Env { _freshCounter :: Integer,
                       _typeEnv      :: Map String (BaseType phase),
                       _declarations :: Map String (Decl phase),
                       _solDecls     :: Map String SolDecl,
                       _allocators   :: Map SolType String,
                       _errors       :: [ErrorCat] }
deriving instance Eq (XType phase) => Eq (Env phase)
deriving instance Show (XType phase) => Show (Env phase)
makeLenses ''Env

type Phase p = (Eq (XType p), Show (XType p), DefinesXType p, Errorable (Error p))

addError :: (Errorable e, Phase p) => e -> State (Env p) ()
addError e = modify $ over errors (toErrorCat e:)

newEnv = Env { _freshCounter = 0,
               _typeEnv = Map.empty,
               _declarations = Map.empty,
               _solDecls = Map.empty,
               _allocators = Map.empty,
               _errors = [] }

freshName :: State (Env phase) String
freshName = do
    i <- freshCounter <<+= 1
    pure $ "v" ++ show i

lookupTypeDecl :: forall p. Phase p => String -> State (Env p) (Decl p)
lookupTypeDecl typeName = do
    decl <- Map.lookup typeName . view declarations <$> get
    case decl of
        Nothing -> do
            addError $ LookupError (LookupErrorType @p typeName)
            pure dummyDecl
        Just tx@TransformerDecl{} -> do
            addError $ LookupError (LookupErrorTypeDecl tx)
            pure dummyDecl
        Just tdec@TypeDecl{} -> pure tdec

modifiers :: Phase p => String -> State (Env p) [Modifier]
modifiers typeName = do
    decl <- lookupTypeDecl typeName
    case decl of
        TypeDecl _ mods _ -> pure mods

isFungible :: (Phase a, Phase b, PhaseTransition a b) => BaseType a -> State (Env b) Bool
isFungible Nat = pure True
isFungible (Named t)  = (Fungible `elem`) <$> modifiers t
-- TODO: Update this for later, because tables should be fungible too?
isFungible _ = pure False

typeOf :: forall p. Phase p => String -> State (Env p) (BaseType p)
typeOf x = do
    maybeT <- Map.lookup x . view typeEnv <$> get
    case maybeT of
        Nothing -> do
            addError $ LookupError @p (LookupErrorVar x)
            pure dummyBaseType
        Just t -> pure t

typeOfLoc :: Phase p => Locator p -> State (Env p) (BaseType p)
typeOfLoc (IntConst _) = pure Nat
typeOfLoc (BoolConst _) = pure PsaBool
typeOfLoc (StrConst _) = pure PsaString
typeOfLoc (AddrConst _) = pure Address
typeOfLoc (Var x) = typeOf x
typeOfLoc (Multiset t _) = pure $ Table [] t
typeOfLoc (Select l k) = do
    lTy <- typeOfLoc l
    kTy <- typeOfLoc k
    keyTypesL <- keyTypes lTy
    if kTy `elem` keyTypesL then
        pure $ valueType lTy
    else
        pure lTy

typeOfLoc (Field l x) = do
    lTy <- typeOfLoc l
    lookupField lTy x

lookupField :: Phase p => BaseType p -> String -> State (Env p) (BaseType p)
lookupField t@(Record key fields) x =
    case [ extractBaseType t | (VarDef y t) <- fields, x == y ] of
        [] -> do
            addError $ FieldNotFoundError x t
            pure Bot
        (fieldTy:_) -> pure fieldTy

lookupField (Named t) x = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> lookupField baseT x

keyTypes :: forall p. Phase p => BaseType p -> State (Env p) [BaseType p]
keyTypes Nat = pure [Nat]
keyTypes PsaBool = pure [PsaBool]
keyTypes PsaString = pure [PsaString]
keyTypes Address = pure [Address]
keyTypes (Named t) = do
    demotedT <- demoteBaseType (Named t)
    pure [Named t, demotedT]

keyTypes table@(Table ["key"] t) = do
    let (Record ["key"] [ VarDef "key" keyT, VarDef "value" _ ]) = extractBaseType @p t
    pure [table, extractBaseType keyT]

keyTypes (Table keys t) = pure [Table keys t]
keyTypes (Record keys fields) = pure $ Record keys fields : [ extractBaseType t | (VarDef x t) <- fields, x `elem` keys ]

valueType :: forall p. Phase p => BaseType p -> BaseType p
valueType Nat = Nat
valueType PsaBool = PsaBool
valueType PsaString = PsaString
valueType Address = Address
valueType (Named t) = Named t
valueType (Table ["key"] t) = let (Record ["key"] [_, VarDef "value" valueTy]) = extractBaseType @p t
                             in extractBaseType valueTy
valueType (Table keys t) = Table keys t
valueType (Record keys fields) =
    case [ VarDef x t | (VarDef x t) <- fields, x `notElem` keys ] of
        [ VarDef _ t ] -> extractBaseType t
        fields -> Record [] fields

demoteBaseType :: Phase p => BaseType p -> State (Env p) (BaseType p)
demoteBaseType Nat = pure Nat
demoteBaseType PsaBool = pure PsaBool
demoteBaseType PsaString = pure PsaString
demoteBaseType Address = pure Address
demoteBaseType (Table keys t) = do
    demotedT <- demoteBaseType (extractBaseType t)
    pure $ Table keys (replaceBaseType t demotedT)

demoteBaseType (Record keys fields) = do
    demotedFields <- mapM (\(VarDef x t) -> do
        demotedT <- demoteBaseType (extractBaseType t)
        pure $ VarDef x (replaceBaseType t demotedT)) fields
    pure $ Record keys demotedFields

demoteBaseType (Named t) = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> demoteBaseType baseT
demoteBaseType Bot = pure Bot

demoteType :: QuantifiedType Compiling -> State (Env Compiling) (QuantifiedType Compiling)
demoteType (q, t) = (q,) <$> demoteBaseType t

-- dummy values that are returned as proxies when errors are encountered
dummyBaseType :: Phase p => BaseType p
dummyBaseType  = Bot

dummyType :: QuantifiedType Compiling
dummyType = (Any, Bot)

dummyDecl :: forall p. Phase p => Decl p
dummyDecl = TypeDecl "unknownDecl__" [] (dummyBaseType @p)

dummySolExpr :: SolExpr
dummySolExpr = SolVar "unknownExpr__"
