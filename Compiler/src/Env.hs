{-# LANGUAGE TemplateHaskell #-}

module Env where

import Control.Lens (makeLenses, over, (<<+=))
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
                 _errorMessages :: [String] }
    deriving (Show, Eq)
makeLenses ''Env

newEnv = Env { _freshCounter = 0,
               _typeEnv = Map.empty,
               _declarations = Map.empty,
               _solDecls = Map.empty,
               _allocators = Map.empty,
               _errorMessages = [] }

freshName :: State Env String
freshName = do
    i <- freshCounter <<+= 1
    pure $ "v" ++ show i

addError :: Error e => e -> State Env ()
addError e = modify $ over errorMessages (prettyStr e:)
