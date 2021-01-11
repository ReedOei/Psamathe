module Error where

import AST

data Error = SyntaxError String
           | TypeError String
           | LookupError String
           | FlowError String
    deriving (Show, Eq)

-- dummy values that are returned as proxies when errors are encountered
dummyBaseType :: BaseType
dummyBaseType = Bot

dummyDecl :: Decl
dummyDecl = TypeDecl "unknownDecl__" [] dummyBaseType

dummySolExpr :: SolExpr
dummySolExpr = SolVar "unknownExpr__"
