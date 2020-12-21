{-# LANGUAGE TemplateHaskell #-}

module Config where

import Control.Lens (makeLenses)

data Config = Config {
        _debug :: Bool
    }
makeLenses ''Config

defaultConfig = Config { _debug = False }

