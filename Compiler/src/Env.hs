{-# LANGUAGE TemplateHaskell #-}

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

