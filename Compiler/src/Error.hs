module Error where

-- TODO: Add more specific error types
data Error = ErrorMessage String
    deriving (Show, Eq)

