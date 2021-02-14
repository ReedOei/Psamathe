{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Phase where

-- Compiler phases
data Preprocessing
data Typechecking
data Compiling

-- Phase transitions - either moving to next phase or staying in current phase
class PhaseTransition a b

instance PhaseTransition Preprocessing Preprocessing
instance PhaseTransition Preprocessing Typechecking

instance PhaseTransition Typechecking Typechecking
instance PhaseTransition Typechecking Compiling

instance PhaseTransition Compiling Compiling
