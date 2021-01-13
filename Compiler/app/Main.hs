{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Lens
import Control.Monad.State
import Control.Monad

import System.Environment

import Text.Parsec

import AST
import Compiler
import Env
import Parser
import Preprocessor
import Typechecker

import Config

compileFile :: Config -> FilePath -> IO ()
compileFile config fileName = do
    content <- readFile fileName
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            let (compiled, env) = runState (compileProg =<< typecheck =<< preprocess prog) newEnv

            if config^.debug > 0 then do
                putStrLn "Processed program:"
                putStrLn $ prettyStr prog
                putStrLn "========================================================"
                putStrLn "========================================================"
                putStrLn "========================================================"
            else pure ()

            if not $ null $ env^.errorMessages then do
                putStrLn "Compilation failed! Errors:"
                mapM_ print $ env^.errorMessages

            else do
                if config^.debug > 0 then do
                    putStrLn "Compiled program:"
                else pure ()

                putStrLn $ prettyStr compiled

            if config^.debug > 1 then print env
            else pure ()

main :: IO ()
main = do
    args <- getArgs

    case args of
        [fname] -> compileFile defaultConfig fname
        _ -> pure ()

