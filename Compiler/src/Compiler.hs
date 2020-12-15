{-# LANGUAGE TemplateHaskell #-}

module Compiler where

import Control.Lens
import Control.Monad.State

import Data.List (intercalate)
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

lookupTypeDecl :: String -> State Env Decl
lookupTypeDecl typeName = do
    decl <- Map.lookup typeName . view declarations <$> get
    case decl of
        Nothing -> error $ "Tried to lookup type declaration " ++ typeName ++ "; not found!"
        Just tx@TransformerDecl{} -> error $ "Tried to lookup type declaration " ++ typeName ++ "; but got: " ++ show tx
        Just tdec@TypeDecl{} -> pure tdec

modifiers :: String -> State Env [Modifier]
modifiers typeName = do
    decl <- lookupTypeDecl typeName
    case decl of
        TypeDecl _ mods _ -> pure mods

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

compileStmt (FlowTransform src (Construct name args) dst) = do
    argsRes <- mapM locate args
    let (newArgs, initArgs) = unzip argsRes
    (srcLoc, srcComp) <- locate src
    (dstLoc, dstComp) <- locate dst
    constructFun <- makeConstructor name
    transfer <- lookupValues newArgs $ \vals -> lookupValue srcLoc $ \_ orig val -> receiveValue orig (constructFun (vals ++ [val])) dstLoc
    pure $ concat initArgs ++ srcComp ++ dstComp ++ transfer

compileStmt (FlowTransform src (Call name args) dst) = do
    argsRes <- mapM locate args
    let (newArgs, initArgs) = unzip argsRes
    (srcLoc, srcComp) <- locate src
    (dstLoc, dstComp) <- locate dst
    transfer <- lookupValues newArgs $ \vals -> lookupValue srcLoc $ \_ orig val -> receiveValue orig (SolCall (SolVar name) (vals ++ [val])) dstLoc
    pure $ concat initArgs ++ srcComp ++ dstComp ++ transfer

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

makeConstructor :: String -> State Env ([SolExpr] -> SolExpr)
makeConstructor t = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ Nat -> pure $ \[arg] -> arg
        TypeDecl _ _ PsaBool -> pure $ \[arg] -> arg
        TypeDecl _ _ PsaString -> pure $ \[arg] -> arg
        TypeDecl _ _ Address -> pure $ \[arg] -> arg
        TypeDecl _ _ (Record _ _) -> pure $ \args -> SolCall (SolVar t) args
        _ -> error $ "Cannot make constructor for: " ++ show decl

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

locate (RecordLit keys members) = do
    newRecord <- freshName
    decl <- declareVar newRecord $ Record keys $ map fst members
    modify $ over typeEnv $ Map.insert newRecord $ Record keys $ map fst members
    initStmts <- concat <$> mapM (locateMember newRecord) members

    pure (Var newRecord, [ SolVarDef decl ] ++ initStmts)
    where
        locateMember newRecord ((x, (_, t)), l) =
            lookupValue l $ \lTy orig src -> do
                pure [ SolAssign (FieldAccess (SolVar newRecord) x) src ]

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

        -- TODO: How to tell whether we are selecting by key or filtering the whole map?
        Table ["key"] (One, Record ["key"] [ ("key", keyTy), ("value", valueTy) ]) -> do
            f (Table ["key"] (One, Record ["key"] [ ("key", keyTy), ("value", valueTy) ]))
                (SolVar x) (SolVar x)

        -- Table ["key"] (One, Record ["key"] [ ("key", keyTy), ("value", valueTy) ]) -> do
        --     idxVarName <- freshName
        --     let idxVar = SolVar idxVarName

        --     body <- f (Table ["key"] (One, Record ["key"] [ ("key", keyTy), ("value", valueTy) ]))
        --             (SolIdx (FieldAccess (SolVar x) "underlying_map")
        --                     (SolIdx (FieldAccess (SolVar x) "keys") idxVar))
        --             (SolIdx (FieldAccess (SolVar x) "underlying_map")
        --                     (SolIdx (FieldAccess (SolVar x) "keys") idxVar))

        --     pure [ For (SolVarDefInit (SolVarDecl (SolTypeName "uint") idxVarName) (SolInt 0))
        --                (SolLt idxVar (FieldAccess (FieldAccess (SolVar x) "keys") "length"))
        --                (SolPostInc idxVar)
        --                body ]

        Record keys fields -> f (Record keys fields) (SolVar x) (SolVar x)

        _ -> error $ "lookupValue Var is not implemented for: " ++ show t

lookupValue (Multiset t elems) f = do
    res <- mapM locate elems
    let (locateds, initStmts) = unzip res
    final <- concat <$> mapM (`lookupValue` f) locateds

    pure $ concat initStmts ++ final

lookupValue (Select l k) f = do
    kTy <- typeOfLoc k
    demotedKTy <- demoteBaseType kTy
    kTyIsFungible <- isFungible kTy

    lookupValue l $ \lTy origL valL -> do
        demotedLTy <- demoteBaseType lTy
        lTyIsFungible <- isFungible lTy

        case demotedLTy of
            Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ])
                | kTy == keyTy -> lookupValue k $ \_ origK valK -> do
                f valueTy (FieldAccess (SolIdx (FieldAccess origL "underlying_map") valK) "value")
                    $ FieldAccess (SolIdx (FieldAccess valL "underyling_map") valK) "value"

            _ ->
                case demotedKTy of
                    Nat | kTyIsFungible -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valK
                        pure [ If (SolLte valK valL) body ]

                    PsaBool -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valK
                        pure [ If (SolEq valL valK) body ]

                    PsaString -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valL
                        pure [ If (SolEq valL valK) body ]

                    Address -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valL
                        pure [ If (SolEq valL valK) body ]

                    Table [] _ -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valL
                        pure [ If (SolEq valL valK) body ]

                    _ -> error $ "lookupValue Select is not implemented for: " ++ show kTy

lookupValue (Filter l q predName args) f = do
    argsRes <- mapM locate args
    let (newArgs, initArgs) = unzip argsRes
    (newL, initL) <- locate l
    lookupValues newArgs $ \vals -> lookupValue newL $ \t orig src -> do
        body <- f t orig src
        argExprs <- mapM buildExpr newArgs
        pure $ concat initArgs ++ initL ++ [ If (SolCall (SolVar predName) (vals ++ [src])) body ]

lookupValue l _ = error $ "lookupValue is not implemented for: " ++ show l

lookupValues :: [Locator] -> ([SolExpr] -> State Env [SolStmt]) -> State Env [SolStmt]
lookupValues [] f = f []
lookupValues (l:ls) f = lookupValue l $ \lTy origL srcL -> lookupValues ls $ \rest -> f (srcL:rest)

receiveValue :: SolExpr -> SolExpr -> Locator -> State Env [SolStmt]
receiveValue orig src (Var x) = do
    t <- typeOf x
    receiveExpr t orig src (SolVar x)

receiveValue orig src (Select l k) = do
    lookupValue (Select l k) $ \ty _ dstExpr ->
        receiveExpr ty orig src dstExpr

receiveValue orig src dst = error $ "Cannot receive values in destination: " ++ show dst

receiveExpr :: BaseType -> SolExpr -> SolExpr -> SolExpr -> State Env [SolStmt]
receiveExpr t orig src dst = do
    demotedT <- demoteBaseType t
    tIsFungible <- isFungible t

    (main, cleanup) <-
        case demotedT of
            Nat | tIsFungible -> pure ([ SolAssign dst (SolAdd dst src) ], [ SolAssign orig (SolSub orig src) ])

            PsaBool | t == PsaBool -> pure ([ SolAssign dst (SolOr dst src) ], [ Delete orig ])

            Table [] _ -> pure ([ ExprStmt (SolCall (FieldAccess dst "push") [ src ] ) ], [ Delete orig ])

            Record keys fields -> pure ([ SolAssign dst src ], [ Delete orig ])

            Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ]) ->
                pure ([ SolAssign (SolIdx (FieldAccess dst "underlying_map") (FieldAccess src "key"))
                                  (FieldAccess src "value")
                      , ExprStmt (SolCall (FieldAccess (FieldAccess dst "keys") "push") [FieldAccess src "key"]) ],
                      [ Delete orig ])

            _ -> error $ "receiveExpr not implemented for: " ++ show demotedT

    if isPrimitiveExpr orig then
        pure main
    else
        pure $ main ++ cleanup

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
toSolType (Table (k:ks) t) = SolTypeName $ encodeBaseType $ Table (k:ks) t
toSolType (Record keys fields) = SolTypeName $ encodeBaseType $ Record keys fields
toSolType (Named t) = SolTypeName t

encodeBaseType :: BaseType -> String
encodeBaseType Nat = "nat"
encodeBaseType PsaBool = "bool"
encodeBaseType PsaString = "string"
encodeBaseType Address = "address"
encodeBaseType (Table keys (q,t)) =
    "table__" ++ intercalate "_" keys ++ "__" ++ show q ++ "__" ++ encodeBaseType t
encodeBaseType (Record keys fields) =
    "record__" ++ intercalate "_" keys ++ "__" ++ intercalate "_" (map go fields)
    where
        go (x,(q,t)) = x ++ "_" ++ show q ++ "_" ++ encodeBaseType t
encodeBaseType (Named t) = t

demoteBaseType :: BaseType -> State Env BaseType
demoteBaseType Nat = pure Nat
demoteBaseType PsaBool = pure PsaBool
demoteBaseType PsaString = pure PsaString
demoteBaseType Address = pure Address
demoteBaseType (Table keys (q, t)) = Table keys . (q,) <$> demoteBaseType t
demoteBaseType (Record keys fields) = Record keys <$> mapM (\(x, (q,t)) -> (x,) . (q,) <$> demoteBaseType t) fields
demoteBaseType (Named t) = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ baseT -> demoteBaseType baseT

typeOfLoc :: Locator -> State Env BaseType
typeOfLoc (IntConst _) = pure Nat
typeOfLoc (BoolConst _) = pure PsaBool
typeOfLoc (StrConst _) = pure PsaString
typeOfLoc (AddrConst _) = pure Address
typeOfLoc (Var x) = typeOf x
typeOfLoc (Multiset t _) = pure $ Table [] t
typeOfLoc (Select l k) = do
    lTy <- typeOfLoc l
    kTy <- typeOfLoc k
    keyTypesL <- keyTypes lTy

    if kTy `elem` keyTypesL then
        pure $ valueType lTy
    else
        pure lTy

keyTypes :: BaseType -> State Env [BaseType]
keyTypes Nat = pure [Nat]
keyTypes PsaBool = pure [PsaBool]
keyTypes PsaString = pure [PsaString]
keyTypes Address = pure [Address]
keyTypes (Named t) = do
    demotedT <- demoteBaseType (Named t)
    pure [Named t, demotedT]
keyTypes t@(Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ])) = pure [t, keyTy]
keyTypes (Table keys t) = pure [Table keys t]
keyTypes (Record keys fields) = pure $ [ Record keys fields ] ++ [ t | (x,(_,t)) <- fields, x `elem` keys ]


valueType :: BaseType -> BaseType
valueType Nat = Nat
valueType PsaBool = PsaBool
valueType PsaString = PsaString
valueType Address = Address
valueType (Named t) = Named t
valueType (Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ])) = valueTy
valueType (Table keys t) = Table keys t
valueType (Record keys fields) =
    case [ (x,t) | (x,t) <- fields, x `notElem` keys ] of
        [ (_,(_,t)) ] -> t
        fields -> Record [] fields

