{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Lens
import Control.Monad.State

import Text.Parsec

import AST
import Compiler
import Env
import Parser
import Preprocessor
import Typechecker

import Config

main :: IO ()
main = compileFile =<< getArgs

compileFile :: Config -> IO ()
compileFile config = do
    content <- readFile $ config^.srcName
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            let (compiled, env) = runState (compileProg =<< typecheck =<< preprocess prog) newEnv

            if config^.debug > 0 then do
                putStrLn "Processed program:"
                putStrLn $ prettyStr prog
                putStrLn "========================================================"
                putStrLn "========================================================"
            else pure ()

            if not $ null $ env^.errors then do
                putStrLn "Compilation failed! Errors:"
                mapM_ print $ env^.errors

            else do
                if config^.debug > 0 then do
                    putStrLn "Compiled program:"
                else pure ()

                putStrLn $ prettyStr compiled

            if config^.debug > 1 then print env
            else pure ()

