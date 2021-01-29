{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

module Env where

import Control.Lens (makeLenses, over, (<<+=), view)
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import AST
import Error

data Env phase = Env { _freshCounter       :: Integer,
                       _typeEnv            :: Map String (BaseType phase),
                       _declarations       :: Map String (Decl phase),
                       _solDecls           :: Map String SolDecl,
                       _allocators         :: Map SolType String,
                       _preprocessorErrors :: [Error Parsed],
                       _typecheckerErrors  :: [Error Preprocessed],
                       _compilerErrors     :: [Error Typechecked] }
deriving instance Eq (XType phase) => Eq (Env phase)
deriving instance Show (XType phase) => Show (Env phase)
makeLenses ''Env

newEnv = Env { _freshCounter = 0,
               _typeEnv = Map.empty,
               _declarations = Map.empty,
               _solDecls = Map.empty,
               _allocators = Map.empty,
               _preprocessorErrors = [],
               _typecheckerErrors = [],
               _compilerErrors = [] }

freshName :: State (Env phase) String
freshName = do
    i <- freshCounter <<+= 1
    pure $ "v" ++ show i

addPreprocessorError :: Error Parsed -> State (Env Parsed) ()
addPreprocessorError e = modify $ over preprocessorErrors (e:)

addTypecheckerError :: Error Preprocessed -> State (Env Preprocessed) ()
addTypecheckerError e = modify $ over typecheckerErrors (e:)

addCompilerError :: Error Typechecked -> State (Env Typechecked) ()
addCompilerError e = modify $ over compilerErrors (e:)

lookupTypeDecl :: String -> State (Env phase) (Decl phase)
lookupTypeDecl typeName = do
    decl <- Map.lookup typeName . view declarations <$> get
    case decl of
        Nothing -> do
            addCompilerError $ LookupError (LookupErrorType typeName)
            pure dummyDecl
        Just tx@TransformerDecl{} -> do
            addCompilerError $ LookupError (LookupErrorTypeDecl tx)
            pure dummyDecl
        Just tdec@TypeDecl{} -> pure tdec

modifiers :: String -> State (Env phase) [Modifier]
modifiers typeName = do
    decl <- lookupTypeDecl typeName
    case decl of
        TypeDecl _ mods _ -> pure mods

isFungible :: BaseType phase -> State (Env phase) Bool
isFungible Nat = pure True
isFungible (Named t) = (Fungible `elem`) <$> modifiers t
-- TODO: Update this for later, because tables should be fungible too?
isFungible _ = pure False

typeOf :: String -> State (Env phase) (BaseType phase)
typeOf x = do
    maybeT <- Map.lookup x . view typeEnv <$> get
    case maybeT of
        Nothing -> do
            addCompilerError $ LookupError (LookupErrorVar x)
            pure dummyBaseType
        Just t -> pure t

typeOfLoc :: Locator phase -> State (Env phase) (BaseType phase)
-- typeOfLoc (IntConst _) = pure Nat
-- typeOfLoc (BoolConst _) = pure PsaBool
-- typeOfLoc (StrConst _) = pure PsaString
-- typeOfLoc (AddrConst _) = pure Address
-- typeOfLoc (Var x) = typeOf x
-- typeOfLoc (Multiset t _) = pure $ Table [] t
-- typeOfLoc (Select l k) = do
--     lTy <- typeOfLoc l
--     kTy <- typeOfLoc k
--     keyTypesL <- keyTypes lTy
--     if kTy `elem` keyTypesL then
--         pure $ valueType lTy
--     else
--         pure lTy

typeOfLoc (Field l x) = do
    lTy <- typeOfLoc l
    lookupField lTy x

lookupField :: BaseType phase -> String -> State (Env phase) (BaseType phase)
lookupField t@(Record key fields) x =
    case [ t | (VarDef y (_,t)) <- fields, x == y ] of
        [] -> do
            addCompilerError $ FieldNotFoundError x t
            pure Bot
        (fieldTy:_) -> pure fieldTy
lookupField (Named t) x = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> lookupField baseT x

keyTypes :: BaseType phase -> State (Env phase) [BaseType phase]
keyTypes Nat = pure [Nat]
keyTypes PsaBool = pure [PsaBool]
keyTypes PsaString = pure [PsaString]
keyTypes Address = pure [Address]
keyTypes (Named t) = do
    demotedT <- demoteBaseType (Named t)
    pure [Named t, demotedT]
keyTypes t@(Table ["key"] (One, Record ["key"] [ VarDef "key" (_,keyTy), VarDef "value" (_,valueTy) ])) = pure [t, keyTy]
keyTypes (Table keys t) = pure [Table keys t]
keyTypes (Record keys fields) = pure $ Record keys fields : [ t | (VarDef x (_,t)) <- fields, x `elem` keys ]

valueType :: BaseType Typechecked -> BaseType Typechecked
valueType Nat = Nat
valueType PsaBool = PsaBool
valueType PsaString = PsaString
valueType Address = Address
valueType (Named t) = Named t
valueType (Table ["key"] (One, Record ["key"] [ VarDef "key" (_,keyTy), VarDef "value" (_,valueTy) ])) = valueTy
valueType (Table keys t) = Table keys t
valueType (Record keys fields) =
    case [ VarDef x t | (VarDef x t) <- fields, x `notElem` keys ] of
        [ VarDef _ (_,t) ] -> t
        fields -> Record [] fields

demoteBaseType :: BaseType Typechecked -> State (Env Typechecked) (BaseType Typechecked)
demoteBaseType Nat = pure Nat
demoteBaseType PsaBool = pure PsaBool
demoteBaseType PsaString = pure PsaString
demoteBaseType Address = pure Address
demoteBaseType (Table keys (q, t)) = Table keys . (q,) <$> demoteBaseType t
demoteBaseType (Record keys fields) = Record keys <$> mapM (\(VarDef x (q,t)) -> VarDef x . (q,) <$> demoteBaseType t) fields
demoteBaseType (Named t) = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> demoteBaseType baseT
demoteBaseType Bot = pure Bot

demoteType :: QuantifiedType Typechecked -> State (Env Typechecked) (QuantifiedType Typechecked)
demoteType (q, t) = (q,) <$> demoteBaseType t

