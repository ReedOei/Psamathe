module Error where

import AST

data Error = SyntaxError String
           | TypeError String
           | LookupError String
           | FlowError String
    deriving (Show, Eq)
