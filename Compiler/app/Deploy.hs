{-# LANGUAGE TemplateHaskell #-}

module Deploy where

import Control.Lens
import Control.Monad

import Text.Parsec (parse, many1, digit, string)

import Data.Either (rights)
import Data.Maybe (fromJust)

import System.Directory (doesFileExist, getCurrentDirectory, listDirectory)
import System.IO (hPutStrLn, stderr, writeFile)
import System.Exit
import System.FilePath
import System.Process

import Config
import AST
import Env

deployFile :: ExecConfig -> String -> IO ()
deployFile config solProg = do
    root <- getProjectRoot
    let contractsDir = joinPath [root, "contracts"]
    let migrationsDir = joinPath [root, "migrations"]

    when (config^.debug > 0) $ do
        putStrLn "Compiled program:"
        putStrLn solProg

    let fileName = takeFileName $ fromJust $ config^.srcName
    let jsFile = replaceExtension fileName "js"
    let solFile = replaceExtension fileName "sol"
    writeFile (joinPath [contractsDir, solFile]) solProg

    let migrationsDir = joinPath [root, "migrations"]
    migrationNum <- getMigrationNum jsFile migrationsDir
    writeMigration migrationsDir jsFile migrationNum
    runMigration migrationNum migrationsDir

getProjectRoot :: IO FilePath
getProjectRoot = getCurrentDirectory >>= getProjectRoot'
    where
        getProjectRoot' curr = do
            let parent = takeDirectory curr
            if curr == parent then do
                error "Current directory is not part of a truffle project. Did you run psamathe --init?"
            else do
                isRoot <- doesFileExist (joinPath [curr, "truffle-config.js"])
                if isRoot then pure curr else getProjectRoot' parent

getMigrationNum :: FilePath -> FilePath -> IO Integer
getMigrationNum fileName migrationsDir = do
    migrations <- filter (isExtensionOf "js") <$> listDirectory migrationsDir
    let migrationExists = rights $ map (parse (many1 digit <* string ('_' : fileName)) "") migrations
    if not . null $ migrationExists then
        pure $ read $ head migrationExists
    else do
        let migrationNums = rights $ map (parse (many1 digit) "") migrations
        if null migrationNums then
            pure 1
        else
            pure $ maximum (map read migrationNums) + 1

writeMigration :: FilePath -> FilePath -> Integer -> IO ()
writeMigration migrationsDir fileName num = do
    let migration = buildMigration $ dropExtension fileName
    writeFile (joinPath [migrationsDir, show num ++ '_' : fileName]) migration

buildMigration :: FilePath -> String
buildMigration name = unlines [
    "const " ++ name ++ " = artifacts.require(\"" ++ name ++ "/C\");",
    "module.exports = function (deployer) {",
    "   deployer.deploy(" ++ name ++ ");",
    "};"]

runMigration :: Integer -> FilePath -> IO ()
runMigration migrationNum migrationsDir = do
    (exitCode, stdout, stderr) <- readProcessWithExitCode "truffle" ["migrate", "-f", show migrationNum, "--to", show migrationNum] ""
    putStrLn stdout
