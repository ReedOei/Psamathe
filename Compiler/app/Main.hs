{-# LANGUAGE TemplateHaskell #-}

module Main where

import Paths_Psamathe

import Control.Lens
import Control.Monad.State
import Control.Monad

import System.FilePath
import System.IO
import System.Process

import Text.Parsec (parse)

import AST
import Compiler
import Env
import Error
import Parser
import Phase
import Preprocessor
import Transform
import Typechecker

import Config
import Deploy

main :: IO ()
main = do
    config <- getArgs
    case config of
        Init -> initialize
        Exec execConfig -> deployFile execConfig =<< compileFile execConfig

putError :: String -> IO ()
putError = hPutStrLn stderr

initialize :: IO ()
initialize = do
    (_, stdout, _) <- readProcessWithExitCode "truffle" ["init"] ""
    config <- readFile =<< getDataFileName (joinPath ["data", "default-config.js"])
    writeFile "truffle-config.js" config
    putStrLn stdout

compileFile :: ExecConfig -> IO String
compileFile config = do
    content <- obtainContent config
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            debugPretty config "Parsed program:" prog

            let (compiled, env) = runState (preprocess prog) (newEnv Preprocessor) >>> typecheck >>> compileProg

            if config^.debug > 1 then print env
            else pure ()

            if not $ null $ env^.errors then
                error $ prettyStr $ env^.errors
            else
                pure $ prettyStr compiled

obtainContent :: ExecConfig -> IO String
obtainContent config =
    case config^.srcName of
        Just "-" -> getContents
        Nothing -> getContents
        Just path -> readFile path

debugPretty :: PrettyPrint a => ExecConfig -> String -> a -> IO a
debugPretty config message x = do
    if config^.debug > 0 then do
        putStrLn message
        putStrLn $ prettyStr x
        putStrLn "========================================================"
        putStrLn "========================================================"
    else pure ()

    pure x
