{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Lens
import Control.Monad.State
import Control.Monad

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
            debugPretty config "Parsed program:" prog

            let (compiled, env) = runState (compileProg =<< typecheck =<< preprocess prog) newEnv

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

debugPretty :: PrettyPrint a => Config -> String -> a -> IO a
debugPretty config message x = do
    if config^.debug > 0 then do
        putStrLn message
        putStrLn $ prettyStr x
        putStrLn "========================================================"
        putStrLn "========================================================"
    else pure ()

    pure x

