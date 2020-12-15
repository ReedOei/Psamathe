{-# LANGUAGE TemplateHaskell #-}

module Compiler where

import Control.Lens
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map

import AST

data Env = Env { _freshCounter :: Integer,
                 _typeEnv :: Map String BaseType,
                 _declarations :: Map String Decl,
                 _solDecls :: Map String SolDecl }
    deriving (Show, Eq)
makeLenses ''Env

newEnv = Env { _freshCounter = 0,
               _typeEnv = Map.empty,
               _declarations = Map.empty,
               _solDecls = Map.empty }

freshName :: State Env String
freshName = do
    i <- freshCounter <<+= 1
    pure $ "v" ++ show i

freshVar :: State Env Locator
freshVar = Var <$> freshName

typeOf :: String -> State Env BaseType
typeOf x = do
    maybeT <- Map.lookup x . view typeEnv <$> get
    case maybeT of
        Nothing -> error $ "Tried to lookup variable " ++ x ++ " in the type environment; not found!"
        Just t -> pure t

modifiers :: String -> State Env [Modifier]
modifiers typeName = do
    decl <- Map.lookup typeName . view declarations <$> get
    case decl of
        Nothing -> error $ "Tried to lookup type declaration " ++ typeName ++ "; not found!"
        Just tx@TransformerDecl{} -> error $ "Tried to lookup type declaration " ++ typeName ++ "; but got: " ++ show tx
        Just (TypeDecl _ mods _) -> pure mods

buildExpr :: Locator -> State Env SolExpr
buildExpr (Var s) = pure $ SolVar s
buildExpr l = error $ "Unsupported locator: " ++ show l

compileProg :: Program -> State Env Contract
compileProg (Program decls mainBody) = do
    mapM_ compileDecl decls
    compiledDecls <- map snd . Map.toList . view solDecls <$> get
    stmts <- concat <$> mapM compileStmt mainBody
    pure $ Contract "0.7.5" "C" $ compiledDecls ++ [Constructor [] stmts]

compileDecl :: Decl -> State Env ()
compileDecl decl@(TypeDecl name ms baseT) = do
    modify $ over declarations $ Map.insert name decl
    -- TODO: Need to generate the struct too
compileDecl decl@(TransformerDecl name args ret body) = do
    modify $ over declarations $ Map.insert name decl

    solArgs <- concat <$> mapM toSolArg args
    rets <- toSolArg ret

    modify $ over typeEnv $ Map.union $ Map.fromList [ (x, t) | (x,(_,t)) <- ret : args ]
    bodyStmts <- concat <$> mapM compileStmt body
    modify $ set typeEnv Map.empty

    modify $ over solDecls $ Map.insert name (Function name solArgs Internal rets bodyStmts)

compileStmt :: Stmt -> State Env [SolStmt]
compileStmt (Flow src dst) = do
    (srcLoc, srcComp) <- locate src
    (dstLoc, dstComp) <- locate dst
    transfer <- lookupValue srcLoc $ \_ orig val -> receiveValue orig val dstLoc

    pure $ srcComp ++ dstComp ++ transfer

compileStmt (FlowTransform src transformer dst) = error "unimplemented!"

compileStmt (Try tryBlock catchBlock) = do
    origEnv <- view typeEnv <$> get
    let origVars = Map.keys origEnv

    tryCompiled <- concat <$> mapM compileStmt tryBlock
    modify $ over typeEnv $ Map.filterWithKey (\k _ -> k `Map.member` origEnv)

    catchCompiled <- concat <$> mapM compileStmt catchBlock
    modify $ over typeEnv $ Map.filterWithKey (\k _ -> k `Map.member` origEnv)

    closureName <- ("closure_"++) <$> freshName

    closureArgs <- makeClosureArgs origVars
    closureRets <- makeClosureRets origVars
    unpackClosureBlock <- makeUnpackClosureBlock origVars
    packClosureBlock <- makePackClosureBlock origVars

    modify $ over solDecls $ Map.insert closureName
           $ Function closureName closureArgs Public closureRets $ tryCompiled ++ packClosureBlock

    pure $ [ SolTry (SolCall (FieldAccess (SolVar "this") closureName) (map SolVar origVars))
                    closureRets
                    unpackClosureBlock
                    catchCompiled ]

makeClosureArgs :: [String] -> State Env [SolVarDecl]
makeClosureArgs vars = mapM go vars
    where
        go x = declareVar x =<< typeOf x

makeClosureRets :: [String] -> State Env [SolVarDecl]
makeClosureRets vars = mapM go vars
    where
        go x = declareVar (x ++ "_out") =<< typeOf x

makeUnpackClosureBlock :: [String] -> State Env [SolStmt]
makeUnpackClosureBlock vars = concat <$> mapM go vars
    where
        go x = pure [ SolAssign (SolVar x) (SolVar (x ++ "_out")) ]

makePackClosureBlock :: [String] -> State Env [SolStmt]
makePackClosureBlock vars = concat <$> mapM go vars
    where
        go x = pure [ SolAssign (SolVar (x ++ "_out")) (SolVar x) ]

locate :: Locator -> State Env (Locator, [SolStmt])
locate (NewVar x t) = do
    modify $ over typeEnv (Map.insert x t)
    decl <- declareVar x t
    pure (Var x, [SolVarDef decl])
locate l = pure (l, [])

lookupValue :: Locator -> (BaseType -> SolExpr -> SolExpr -> State Env [SolStmt]) -> State Env [SolStmt]
lookupValue (IntConst i) f = f Nat (SolInt i) (SolInt i)
lookupValue (BoolConst b) f = f PsaBool (SolBool b) (SolBool b)
lookupValue (StrConst s) f = f PsaString (SolStr s) (SolStr s)
lookupValue (AddrConst addr) f = f Address (SolAddr addr) (SolAddr addr)
lookupValue (Var x) f = do
    t <- typeOf x
    case t of
        Nat -> f Nat (SolVar x) (SolVar x)
        PsaBool -> f PsaBool (SolVar x) (SolVar x)
        PsaString -> f PsaString (SolVar x) (SolVar x)
        Address -> f Address (SolVar x) (SolVar x)
        Table [] (_,t) -> do
            idxVarName <- freshName
            let idxVar = SolVar idxVarName

            body <- f t (SolIdx (SolVar x) idxVar) (SolIdx (SolVar x) idxVar)

            pure [ For (SolVarDefInit (SolVarDecl (SolTypeName "uint") idxVarName) (SolInt 0))
                       (SolLt idxVar (FieldAccess (SolVar x) "length"))
                       (SolPostInc idxVar)
                       body ]

        _ -> error $ "lookupValue Var is not implemented for: " ++ show t

lookupValue (Multiset t elems) f = concat <$> mapM (`lookupValue` f) elems

lookupValue (Select l k) f = do
    lookupValue k $ \kTy origK valK -> do
        demotedT <- demoteBaseType kTy
        tIsFungible <- isFungible kTy
        case demotedT of
            Nat | tIsFungible -> lookupValue l $ \lTy origL valL -> do
                body <- f lTy origL valK
                pure [ If (SolLte valK valL) body ]

            PsaBool -> lookupValue l $ \lTy origL valL -> do
                body <- f lTy origL valK
                pure [ If (SolEq valL valK) body ]

            _ -> error $ "lookupValue Select is not implemented for: " ++ show kTy

lookupValue l _ = error $ "lookupValue is not implemented for: " ++ show l

receiveValue :: SolExpr -> SolExpr -> Locator -> State Env [SolStmt]
receiveValue orig src (Var x) = do
    t <- typeOf x
    demotedT <- demoteBaseType t
    tIsFungible <- isFungible t

    main <-
        case demotedT of
            Nat | tIsFungible -> pure [ SolAssign (SolVar x) (SolAdd (SolVar x) src) ]

            PsaBool | t == PsaBool -> pure [ SolAssign (SolVar x) (SolOr (SolVar x) src) ]

            Table [] _ ->
                pure [ ExprStmt (SolCall (FieldAccess (SolVar x) "push") [ src ] ) ]

            _ -> error "Not implemented!"

    let cleanup = if isPrimitiveExpr orig then [] else [ Delete orig ]

    pure $ main ++ cleanup

receiveValue orig src dst = error $ "Cannot receive values in destination: " ++ show dst

declareVar :: String -> BaseType -> State Env SolVarDecl
declareVar x t = do
    demotedT <- demoteBaseType t
    if isPrimitive demotedT then
        pure $ SolVarDecl (toSolType t) x
    else
        -- TODO: Might need to change this so it's not always memory...
        pure $ SolVarLocDecl (toSolType t) Memory x

toSolArg :: VarDef -> State Env [SolVarDecl]
-- TODO: May need to generate multiple var decls per vardef b/c of Solidity (numerous) shortcomings regarding structs
toSolArg (x,(_,t)) = do
    decl <- declareVar x t
    pure [decl]

isPrimitiveExpr :: SolExpr -> Bool
isPrimitiveExpr (SolInt _) = True
isPrimitiveExpr (SolBool _) = True
isPrimitiveExpr (SolStr _) = True
isPrimitiveExpr (SolAddr _) = True
isPrimitiveExpr _ = False

isPrimitive :: BaseType -> Bool
isPrimitive Nat = True
isPrimitive PsaBool = True
isPrimitive PsaString = True
isPrimitive Address = True
isPrimitive _ = False

isFungible :: BaseType -> State Env Bool
isFungible Nat = pure True
isFungible (Named t) = (Fungible `elem`) <$> modifiers t
-- TODO: Update this for later, because tables should be fungible too?
isFungible _ = pure False

toSolType :: BaseType -> SolType
toSolType Nat = SolTypeName "uint"
toSolType PsaBool = SolTypeName "bool"
toSolType PsaString = SolTypeName "string"
toSolType Address = SolTypeName "address"
toSolType (Table [] (_, t)) = SolArray $ toSolType t

demoteBaseType :: BaseType -> State Env BaseType
demoteBaseType Nat = pure Nat
demoteBaseType PsaBool = pure PsaBool
demoteBaseType PsaString = pure PsaString
demoteBaseType Address = pure Address
demoteBaseType (Table keys (q, t)) = Table keys . (q,) <$> demoteBaseType t
demoteBaseType t = error $ "demoteBaseType called with " ++ show t

