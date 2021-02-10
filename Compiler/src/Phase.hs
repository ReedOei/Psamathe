{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Phase where

-- Compiler phases
data Parsed
data Preprocessed
data Typechecked
data Compiled

-- Phase transitions - either moving to next phase or staying in current phase
class PhaseTransition a b

instance PhaseTransition Parsed Parsed
instance PhaseTransition Parsed Preprocessed

instance PhaseTransition Preprocessed Preprocessed
instance PhaseTransition Preprocessed Typechecked

instance PhaseTransition Typechecked Typechecked
