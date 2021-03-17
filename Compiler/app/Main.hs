{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Lens
import Control.Monad.State
import Control.Monad

import Text.Parsec (parse)

import Data.Maybe (fromJust)

import System.Directory (createDirectoryIfMissing)
import System.IO (hPutStrLn, stderr, writeFile)
import System.Exit
import System.FilePath

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

main :: IO ()
main = do
    config <- getArgs
    result <- compileFile config
    case result of
        Left err -> do
            putError "Compilation failed!"
            putError "-------------------"
            putError $ prettyStr err
            exitFailure
        Right prog -> do
            when (config^.debug > 0) $ do
                putStrLn "Compiled program:"
                putStrLn prog
            let fileName = takeFileName $ fromJust $ config^.srcName
            createDirectoryIfMissing True "__psacache__"
            writeFile (joinPath ["__psacache__", replaceExtension fileName "sol"]) prog

putError = hPutStrLn stderr

compileFile :: Config -> IO (Either [ErrorCat] String)
compileFile config = do
    content <- obtainContent config
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            debugPretty config "Parsed program:" prog

            let (compiled, env) = runState (preprocess prog) (newEnv Preprocessor) >>> typecheck >>> compileProg

            if config^.debug > 1 then print env
            else pure ()

            if not $ null $ env^.errors then pure . Left $ env^.errors
            else pure . Right $ prettyStr compiled

obtainContent :: Config -> IO String
obtainContent config =
    case config^.srcName of
        Just "-" -> getContents
        Nothing -> getContents
        Just path -> readFile path

debugPretty :: PrettyPrint a => Config -> String -> a -> IO a
debugPretty config message x = do
    if config^.debug > 0 then do
        putStrLn message
        putStrLn $ prettyStr x
        putStrLn "========================================================"
        putStrLn "========================================================"
    else pure ()

    pure x

