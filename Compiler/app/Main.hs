module Main where

import Control.Monad.State
import Control.Monad

import Data.List (intercalate)

import Text.Parsec

import AST
import Parser
import Compiler

compileFile fileName = do
    content <- readFile fileName
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            putStrLn $ prettyStr prog

            let (compiled, env) = runState (compileProg prog) newEnv

            putStrLn $ prettyStr compiled
            putStrLn "========================================================"
            putStrLn "========================================================"
            putStrLn "========================================================"
            print env

main :: IO ()
main = pure ()

