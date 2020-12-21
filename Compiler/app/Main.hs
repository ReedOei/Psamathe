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

import Config

compileFile :: Config -> FilePath -> IO ()
compileFile config fileName = do
    content <- readFile fileName
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            let (compiled, env) = runState (compileProg prog) newEnv

            if config^.debug then do
                putStrLn "Processed program:"
                putStrLn $ prettyStr prog
                putStrLn "========================================================"
                putStrLn "========================================================"
                putStrLn "========================================================"

                putStrLn "Compiled program:"
            else
                pure ()

            putStrLn $ prettyStr compiled

main :: IO ()
main = do
    args <- getArgs

    case args of
        [fname] -> compileFile defaultConfig fname
        _ -> pure ()

