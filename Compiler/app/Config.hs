{-# LANGUAGE TemplateHaskell #-}

module Config where

import Control.Lens (makeLenses)

import Data.Maybe (fromMaybe)

import Options.Applicative as Opt

data ExecConfig = ExecConfig {
    _debug :: Integer,
    _srcName :: Maybe FilePath
}

data Config = Exec ExecConfig | Init
makeLenses ''ExecConfig

configParser :: Opt.Parser Config
configParser = initMode <|> execMode
    where
        execMode = Exec <$> (ExecConfig <$>
            flag 0 1 (long "debug" <> short 'd' <> help "Debug level to use; higher is more verbose.")
            <*> optional (argument str (metavar "FILE" <> help "The main file to compile. Pass `-` to force reading input from stdin.")))
        initMode = flag' Init (short 'i' <> long "init" <> help "Initialize current directory as a truffle project and setup truffle-config.js.")

getArgs = execParser opts
    where
        opts = info (configParser <**> helper)
                (fullDesc <>
                 progDesc "Psamathe is a blockchain programming language." <>
                 header "psamathe")
