{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Env where

import Control.Lens (makeLenses, over, (<<+=), view)
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import AST
import Error

data Env = Env { _freshCounter  :: Integer,
                 _typeEnv       :: Map String BaseType,
                 _declarations  :: Map String Decl,
                 _solDecls      :: Map String SolDecl,
                 _allocators    :: Map SolType String,
                 _errors :: [Error] }
    deriving (Show, Eq)
makeLenses ''Env

newEnv = Env { _freshCounter = 0,
               _typeEnv = Map.empty,
               _declarations = Map.empty,
               _solDecls = Map.empty,
               _allocators = Map.empty,
               _errors = [] }

freshName :: State Env String
freshName = do
    i <- freshCounter <<+= 1
    pure $ "v" ++ show i

addError :: Error -> State Env ()
addError e = modify $ over errors (e:)

lookupTypeDecl :: String -> State Env Decl
lookupTypeDecl typeName = do
    decl <- Map.lookup typeName . view declarations <$> get
    case decl of
        Nothing -> do
            addError $ LookupError (LookupErrorType typeName)
            pure dummyDecl
        Just tx@TransformerDecl{} -> do
            addError $ LookupError (LookupErrorTypeDecl tx)
            pure dummyDecl
        Just tdec@TypeDecl{} -> pure tdec

modifiers :: String -> State Env [Modifier]
modifiers typeName = do
    decl <- lookupTypeDecl typeName
    case decl of
        TypeDecl _ mods _ -> pure mods

typeOf :: String -> State Env BaseType
typeOf x = do
    maybeT <- Map.lookup x . view typeEnv <$> get
    case maybeT of
        Nothing -> do
            addError $ LookupError (LookupErrorVar x)
            pure dummyBaseType
        Just t -> pure t

typeOfLoc :: Locator -> State Env BaseType
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

lookupField :: BaseType -> String -> State Env BaseType
lookupField t@(Record key fields) x =
    case [ t | (y,(_,t)) <- fields, x == y ] of
        [] -> do
            addError $ FieldNotFoundError x t
            pure Bot
        (fieldTy:_) -> pure fieldTy
lookupField (Named t) x = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> lookupField baseT x

keyTypes :: BaseType -> State Env [BaseType]
keyTypes Nat = pure [Nat]
keyTypes PsaBool = pure [PsaBool]
keyTypes PsaString = pure [PsaString]
keyTypes Address = pure [Address]
keyTypes (Named t) = do
    demotedT <- demoteBaseType (Named t)
    pure [Named t, demotedT]
keyTypes t@(Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ])) = pure [t, keyTy]
keyTypes (Table keys t) = pure [Table keys t]
keyTypes (Record keys fields) = pure $ Record keys fields : [ t | (x,(_,t)) <- fields, x `elem` keys ]

valueType :: BaseType -> BaseType
valueType Nat = Nat
valueType PsaBool = PsaBool
valueType PsaString = PsaString
valueType Address = Address
valueType (Named t) = Named t
valueType (Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ])) = valueTy
valueType (Table keys t) = Table keys t
valueType (Record keys fields) =
    case [ (x,t) | (x,t) <- fields, x `notElem` keys ] of
        [ (_,(_,t)) ] -> t
        fields -> Record [] fields

demoteBaseType :: BaseType -> State Env BaseType
demoteBaseType Nat = pure Nat
demoteBaseType PsaBool = pure PsaBool
demoteBaseType PsaString = pure PsaString
demoteBaseType Address = pure Address
demoteBaseType (Table keys (q, t)) = Table keys . (q,) <$> demoteBaseType t
demoteBaseType (Record keys fields) = Record keys <$> mapM (\(x, (q,t)) -> (x,) . (q,) <$> demoteBaseType t) fields
demoteBaseType (Named t) = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> demoteBaseType baseT
demoteBaseType Bot = pure Bot

demoteType :: Type -> State Env Type
demoteType (q, t) = (q,) <$> demoteBaseType t

