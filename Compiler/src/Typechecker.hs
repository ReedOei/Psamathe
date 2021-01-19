{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Typechecker where

import Control.Lens (view)
import Control.Monad.State

import Data.List (nub, sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Ord (comparing)
import Data.Semilattice.Join

import AST
import Env
import Error

isPrimitive :: BaseType -> Bool
isPrimitive Nat = True
isPrimitive PsaBool = True
isPrimitive PsaString = True
isPrimitive Address = True
isPrimitive _ = False

isFungible :: BaseType -> State Env Bool
isFungible Nat = pure True
isFungible (Named t) = (Fungible `elem`) <$> modifiers t
-- TODO: Update this for later, because tables should be fungible too?
isFungible _ = pure False

isAsset :: BaseType -> State Env Bool
isAsset (Named t) = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ ms baseT -> do
            baseAsset <- isAsset baseT
            pure $ Asset `elem` ms || baseAsset
isAsset (Record _ fields) = or <$> mapM (\(_,(_,t)) -> isAsset t) fields
isAsset (Table _ (_,t)) = isAsset t
isAsset _ = pure False

instance Join TyQuant where
    Any \/ _ = Any
    _ \/ Any = Any
    One \/ Nonempty = Nonempty
    Nonempty \/ One = Nonempty
    x \/ y
        | x == y = x
        | otherwise = Any

instance Join BaseType where
    Table ks1 t1 \/ Table ks2 t2 =
        case t1 \/ t2 of
            (_, Bot) -> Bot
            t' -> Table (nub (ks1 ++ ks2)) t'
    Record ks1 fs1 \/ Record ks2 fs2 =
        if length fs1 /= length fs2 then Bot
        else if any ((== Bot) . snd . snd) fs' then Bot
        else Record ks' fs'
        where
            ks' = nub $ ks1 ++ ks2
            fs' = do
                let fs1' = sortBy (comparing fst) fs1
                let fs2' = sortBy (comparing fst) fs1
                ((x, t1), (y, t2)) <- zip fs1' fs2'
                if x == y then
                    pure (x, t1 \/ t2)
                else
                    pure (x, (Any, Bot))

    t1 \/ t2
        | t1 == t2 = t1
        | otherwise = Bot

instance Join Type where
    (q1,t1) \/ (q2,t2) = (q1 \/ q2, t1 \/ t2)

type TypeEnv = Map String Type

instance Join TypeEnv where
    gamma \/ delta = Map.unionWith (\/) gamma delta

-- | Combines type environments using joins, but drops all variables that are not in **BOTH**
--   environments. Fails with an error if this would require dropping any assets
mergeTypeEnv :: TypeEnv -> TypeEnv -> State Env TypeEnv
mergeTypeEnv gamma delta = do
    gammaDropErrs <- fmap concat $ mapM safeDrop $ Map.elems $ Map.difference gamma delta
    mapM_ addError gammaDropErrs

    deltaDropErrs <- fmap concat $ mapM safeDrop $ Map.elems $ Map.difference delta gamma
    mapM_ addError deltaDropErrs

    pure $ Map.intersectionWith (\/) gamma delta

safeDrop :: Type -> State Env [Error]
safeDrop (Empty,_) = pure []
safeDrop (q,t) = do
    assetTy <- isAsset t
    pure $ if assetTy then [AssetDropError (q,t)] else []

-- TODO: Probably want to have multiple AST types for better type safety
typecheck :: Program -> State Env Program
typecheck prog@(Program decls stmts) = do
    -- NOTE: May need to/want to transform program
    mapM_ checkDecl decls
    mapM_ checkStmt stmts
    pure prog

checkDecl :: Decl -> State Env ()
checkDecl (TransformerDecl _name _args _ret _body) = pure ()
checkDecl (TypeDecl _name modifiers _baseT) = do
    validModifiers modifiers
    pure ()

validModifiers :: [Modifier] -> State Env ()
validModifiers _ = pure ()

checkStmt :: Stmt -> State Env ()
checkStmt _ = pure ()

