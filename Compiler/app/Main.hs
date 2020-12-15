module Main where

import Control.Monad.State
import Control.Monad

import Data.List (intercalate)

import System.Environment

import Text.Parsec

import AST
import Parser
import Compiler

compileFile debug fileName = do
    content <- readFile fileName
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            let (compiled, env) = runState (compileProg prog) newEnv

            if debug then do
                putStrLn "Processed program:"
                putStrLn $ prettyStr prog
                putStrLn "========================================================"
                putStrLn "========================================================"
                putStrLn "========================================================"

                putStrLn "Compiled program:"
            else
                pure()

            putStrLn $ prettyStr compiled

main :: IO ()
main = do
    args <- getArgs

    case args of
        [fname] -> compileFile False fname
        _ -> pure ()

