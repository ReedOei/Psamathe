{-# LANGUAGE TemplateHaskell #-}

module Config where

import Control.Lens (makeLenses)

import Data.Maybe (fromMaybe)

import Options.Applicative as Opt

data Config = Config {
        _debug :: Integer,
        _srcName :: FilePath
    }
makeLenses ''Config

configParser :: Opt.Parser Config
configParser = Config
    <$> flag 0 1 (long "debug" <> short 'd' <> help "Debug level to use; higher is more verbose.")
    <*> argument str (metavar "FILE")

getArgs = execParser opts
    where
        opts = info (configParser <**> helper)
                (fullDesc <>
                 progDesc "Psamathe is a blockchain programming language." <>
                 header "psamathe")

