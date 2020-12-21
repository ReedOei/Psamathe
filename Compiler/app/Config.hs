{-# LANGUAGE TemplateHaskell #-}

module Config where

import Control.Lens (makeLenses)

data Config = Config {
        _debug :: Integer
    }
makeLenses ''Config

defaultConfig = Config { _debug = 0 }

