{-# LANGUAGE TupleSections #-}

module Compiler where

-- TODO: Also, need to clean up **all** non-return vars when exiting the function, probably. BUT BE CAREFUL WITH storage VARIABLES!!!
-- TODO: Remove the keyset check for destination (e.g., a --> b[k]) should allocate k in `b` if `b` is a map, to match one of Solidity's few useful behaviors
-- TODO: Check that assigning maps/arrays/records works fine
-- TODO: Try to flow entire maps between each other
-- TODO: Ensure that the `keys` and `keyset` and everything gets udpated properly
-- TODO: Check that deletes are right too
-- TODO: Remove delete from things that cause compilation to fail
-- TODO: Make parser to use Parsec's symbol thing properly
-- TODO: Reorganize tests into actual Haskell tests
-- TODO: Add .travis.yml configuration for actually testing the Haskell compiler, and make the Travis build work in general

import Control.Lens hiding (Empty)
import Control.Monad.State

import Data.List (intercalate)
import Data.Map (Map)
import Data.Traversable
import qualified Data.Map as Map

import Debug.Trace

import AST
import Env
import Error
import Typechecker

freshVar :: State Env Locator
freshVar = Var <$> freshName

allocateNew :: SolType -> State Env (SolExpr, [SolStmt])
allocateNew t = do
    curState <- Map.lookup t . view allocators <$> get
    allocator <- case curState of
        Nothing -> do
            allocator <- freshName
            modify $ over allocators $ Map.insert t allocator
            pure allocator
        Just allocator -> pure allocator

    pure (SolCall (FieldAccess (SolVar allocator) "push") [], [])

buildExpr :: Locator -> State Env SolExpr
buildExpr (Var s) = pure $ SolVar s
buildExpr l = do
    addError $ SyntaxError ("Unsupported locator: " ++ show l)
    pure dummySolExpr

compileProg :: Program -> State Env Contract
compileProg (Program decls mainBody) = do
    mapM_ compileDecl decls
    stmts <- concat <$> mapM compileStmt mainBody
    compiledDecls <- Map.elems . view solDecls <$> get
    allocators <- Map.toList . view allocators <$> get
    let allocatorDecls = [ FieldDef (SolVarDecl (SolArray t) x) | (t,x) <- allocators ]
    pure $ Contract "0.7.5" "C" $ allocatorDecls ++ compiledDecls ++ [Constructor [] stmts]

compileDecl :: Decl -> State Env ()
compileDecl decl@(TypeDecl name _ baseT) = do
    modify $ over declarations $ Map.insert name decl
    defineStruct name baseT

compileDecl decl@(TransformerDecl name args ret body) = do
    modify $ over declarations $ Map.insert name decl

    solArgs <- concat <$> mapM toSolArg args
    rets <- toSolArg ret

    modify $ over typeEnv $ Map.union $ Map.fromList [ (x, t) | (x,(_,t)) <- ret : args ]
    bodyStmts <- concat <$> mapM compileStmt body
    modify $ set typeEnv Map.empty

    modify $ over solDecls $ Map.insert name (Function name solArgs Internal rets bodyStmts)

defineStruct :: String -> BaseType -> State Env ()
defineStruct name Nat = pure ()
defineStruct name PsaBool = pure ()
defineStruct name PsaString = pure ()
defineStruct name Address = pure ()
defineStruct name (Record _ fields) = do
    newStruct <- Struct name . (SolVarDecl (SolTypeName "bool") "initialized":) <$> mapM (\(x,(_,t)) -> SolVarDecl <$> toSolType t <*> pure x) fields
    modify $ over solDecls $ Map.insert name newStruct
defineStruct name ty@(Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valTy)) ])) = do
    solKeyTy <- toSolType keyTy
    solValTy <- toSolType valTy
    let newStruct = Struct name [
                        SolVarDecl (SolMapping solKeyTy solValTy) "underlying_map",
                        SolVarDecl (SolMapping solKeyTy (SolTypeName "bool")) "keyset",
                        SolVarDecl (SolArray solKeyTy) "keys"
                    ]
    modify $ over solDecls $ Map.insert name newStruct
defineStruct name t = do
    addError $ TypeError "Cannot create struct for" t

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

    pure [ SolTry (SolCall (FieldAccess (SolVar "this") closureName) (map SolVar origVars))
                    closureRets
                    unpackClosureBlock
                    catchCompiled ]

compileStmt Revert = pure [ SolRevert (SolStr "REVERT") ]

makeConstructor :: String -> State Env ([SolExpr] -> SolExpr)
makeConstructor t = do
    decl <- lookupTypeDecl t
    case decl of
        TypeDecl _ _ Nat -> pure $ \[arg] -> arg
        TypeDecl _ _ PsaBool -> pure $ \[arg] -> arg
        TypeDecl _ _ PsaString -> pure $ \[arg] -> arg
        TypeDecl _ _ Address -> pure $ \[arg] -> arg
        -- First argument is the "initialized" field
        TypeDecl _ _ (Record _ _) -> pure $ \args -> SolCall (SolVar t) $ SolBool True : args
        TypeDecl _ _ t -> do
            addError $ TypeError "Cannot make constructor for" t
            pure $ \_ -> dummySolExpr
        tx@TransformerDecl{} -> do
            addError $ SyntaxError ("Cannot make constructor for transformer" ++ show tx)
            pure $ \_ -> dummySolExpr

makeClosureArgs :: [String] -> State Env [SolVarDecl]
makeClosureArgs vars = concat <$> mapM go vars
    where
        go x = declareVar x =<< typeOf x

makeClosureRets :: [String] -> State Env [SolVarDecl]
makeClosureRets vars = concat <$> mapM go vars
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
    modify $ over typeEnv $ Map.insert x t
    defs <- defineVar x t
    pure (Var x, defs)

locate (RecordLit keys members) = do
    newRecord <- freshName
    defs <- defineVar newRecord $ Record keys $ map fst members
    modify $ over typeEnv $ Map.insert newRecord $ Record keys $ map fst members
    initStmts <- concat <$> mapM (locateMember newRecord) members

    pure (Var newRecord,
          [ SolAssign (FieldAccess (SolVar newRecord) "initialized") (SolBool True) ]
          ++ defs ++ initStmts)
    where
        locateMember newRecord ((x, (_, t)), l) =
            lookupValue l $ \lTy orig src ->
                receiveExpr t orig src (FieldAccess (SolVar newRecord) x)

locate l = pure (l, [])

lookupValue :: Locator -> (BaseType -> SolExpr -> SolExpr -> State Env [SolStmt]) -> State Env [SolStmt]
lookupValue (IntConst i) f = f Nat (SolInt i) (SolInt i)
lookupValue (BoolConst b) f = f PsaBool (SolBool b) (SolBool b)
lookupValue (StrConst s) f = f PsaString (SolStr s) (SolStr s)
lookupValue (AddrConst addr) f = f Address (SolAddr addr) (SolAddr addr)
lookupValue (Var x) f = do
    t <- typeOf x
    sendExpr t (SolVar x) f

lookupValue (Multiset t elems) f = do
    res <- mapM locate elems
    let (locateds, initStmts) = unzip res
    final <- concat <$> mapM (`lookupValue` f) locateds

    pure $ concat initStmts ++ final

lookupValue (Field l x) f = do
    (newL, init) <- locate l
    stmts <- lookupValue newL $ \lTy orig src -> do
        fieldTy <- lookupField lTy x
        sendExpr fieldTy (FieldAccess orig x) f

    pure $ init ++ stmts

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
                body <- f valueTy (SolIdx (FieldAccess origL "underlying_map") valK) (SolIdx (FieldAccess valL "underlying_map") valK)
                pure $ Require (SolIdx (FieldAccess origL "keyset") valK) (SolStr "KEY_NOT_FOUND") : body

            _ ->
                case demotedKTy of
                    Nat | kTyIsFungible -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valK
                        pure $ Require (SolLte valK valL) (SolStr "UNDERFLOW") : body

                    PsaBool -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valK
                        pure $ Require (SolEq valL valK) (SolStr "FAILED TO SELECT") : body

                    PsaString -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valL
                        pure $ Require (SolEq valL valK) (SolStr "FAILED TO SELECT") : body

                    Address -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valL
                        pure $ Require (SolEq valL valK) (SolStr "FAILED TO SELECT") : body

                    -- TODO: This needs to make sure that every element gets found
                    Table [] _ -> lookupValue k $ \_ origK valK -> do
                        body <- f lTy origL valL
                        pure [ If (SolEq valL valK) body ]

                    _ -> do
                        addError $ UnimplementedError "lookupValue Select" (show kTy)
                        pure []

lookupValue (Filter l q predName args) f = do
    argsRes <- mapM locate args
    let (newArgs, initArgs) = unzip argsRes
    (newL, initL) <- locate l
    lookupValues newArgs $ \vals -> lookupValue newL $ \t orig src -> do
        body <- f t orig src
        argExprs <- mapM buildExpr newArgs
        counterName <- freshName
        pure $ [ SolVarDefInit (SolVarDecl (SolTypeName "uint") counterName) (SolInt 0) ]
               ++ concat initArgs
               ++ initL
               ++ [ If (SolCall (SolVar predName) (vals ++ [src]))
                        (ExprStmt (SolPostInc (SolVar counterName)) : body) ]
               ++ [ Require (checkCounter q (SolVar counterName)) (SolStr "FAILED_TO_SELECT_RIGHT_NUM") ]
    where
        checkCounter Empty counter = SolEq counter (SolInt 0)
        checkCounter Any _ = SolBool True
        checkCounter One counter = SolEq counter (SolInt 1)
        checkCounter Nonempty counter = SolLte (SolInt 1) counter

lookupValue l _ = do
    addError $ UnimplementedError "lookupValue" (show l)
    pure []

lookupValues :: [Locator] -> ([SolExpr] -> State Env [SolStmt]) -> State Env [SolStmt]
lookupValues [] f = f []
lookupValues (l:ls) f = lookupValue l $ \lTy origL srcL -> lookupValues ls $ \rest -> f (srcL:rest)

sendExpr :: BaseType -> SolExpr -> (BaseType -> SolExpr -> SolExpr -> State Env [SolStmt]) -> State Env [SolStmt]
sendExpr Nat e f = f Nat e e
sendExpr PsaBool e f  = f PsaBool e e
sendExpr PsaString e f = f PsaString e e
sendExpr Address e f = f Address e e
sendExpr (Table [] (_,t)) e f = do
    idxVarName <- freshName
    let idxVar = SolVar idxVarName

    body <- f t (SolIdx e idxVar) (SolIdx e idxVar)

    -- TODO: Need to be careful deleting in here, because it can lead to issues if we delete multiple elements from the list (i.e., we'll mess up the indexes)
    pure [ For (SolVarDefInit (SolVarDecl (SolTypeName "uint") idxVarName) (SolInt 0))
               (SolLt idxVar (FieldAccess e "length"))
               (SolPostInc idxVar)
               body ]

-- TODO: How to tell whether we are selecting by key or filtering the whole map?
sendExpr (Table ["key"] (One, Record ["key"] [ ("key", keyTy), ("value", valueTy) ])) e f =
    f (Table ["key"] (One, Record ["key"] [ ("key", keyTy), ("value", valueTy) ])) e e
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

sendExpr (Named t) e f = f (Named t) e e

sendExpr (Record keys fields) e f = f (Record keys fields) e e

sendExpr t e f = do
    addError $ UnimplementedError "lookupValue Var" (show t)
    pure []


receiveValue :: SolExpr -> SolExpr -> Locator -> State Env [SolStmt]
receiveValue orig src (Var x) = do
    t <- typeOf x
    receiveExpr t orig src (SolVar x)

receiveValue orig src (Select l k) = do
    lookupValue (Select l k) $ \ty _ dstExpr ->
        receiveExpr ty orig src dstExpr

receiveValue orig src (Field l x) = do
    lookupValue l $ \ty _ dstExpr -> do
        fieldTy <- lookupField ty x
        receiveExpr fieldTy orig src $ FieldAccess dstExpr x

receiveValue orig src dst = do
    addError $ FlowError ("Cannot recieve values in destination" ++ show dst)
    pure []

receiveExpr :: BaseType -> SolExpr -> SolExpr -> SolExpr -> State Env [SolStmt]
receiveExpr t orig src dst = do
    demotedT <- demoteBaseType t
    tIsFungible <- isFungible t
    tIsAsset <- isAsset t

    (main, cleanup) <-
        case demotedT of
            Nat | tIsFungible ->
                pure ([ Require (SolLte dst (SolAdd dst src)) (SolStr "OVERFLOW"),
                        SolAssign dst (SolAdd dst src) ],
                      [ SolAssign orig (SolSub orig src) ])

            Nat -> pure $ handleSelfAssign tIsAsset
                                [ Require (SolEq dst (SolInt 0)) (SolStr "ALREADY_INITIALIZED") ]
                                [ SolAssign dst src ]
                                [ Delete orig ]

            PsaBool | t == PsaBool -> pure ([ SolAssign dst (SolOr dst src) ], [ Delete orig ])

            Address -> pure $ handleSelfAssign tIsAsset
                                    [ Require (SolEq dst (SolAddr "0x0")) (SolStr "ALREADY_INITIALIZED") ]
                                    [ SolAssign dst src ]
                                    [ Delete orig ]

            Table [] _ -> pure ([ ExprStmt (SolCall (FieldAccess dst "push") [ src ] ) ], [ Delete orig ])

            Record keys fields -> pure $ handleSelfAssign tIsAsset
                                            [ Require (SolEq (FieldAccess dst "initialized") (SolBool False)) (SolStr "ALREADY_INITIALIZED") ]
                                            [ SolAssign dst src ]
                                            [ Delete orig ]

            Table ["key"] (One, Record ["key"] [ ("key", (_,keyTy)), ("value", (_,valueTy)) ]) ->
                pure ([ SolAssign (SolIdx (FieldAccess dst "underlying_map") (FieldAccess src "key"))
                                  (FieldAccess src "value"),
                        SolAssign (SolIdx (FieldAccess dst "keyset") (FieldAccess src "key")) (SolBool True),
                        ExprStmt (SolCall (FieldAccess (FieldAccess dst "keys") "push") [FieldAccess src "key"]) ],
                      [ Delete orig ])

            _ -> do
                addError $ FlowError ("receiveExpr not implemented for: " ++ show demotedT)
                pure ([], [])

    pure $ if isPrimitiveExpr orig then main else main ++ cleanup

    where
        -- TODO: Remove this hack once we have a better implementation (see https://github.com/ReedOei/Psamathe/issues/16)
        handleSelfAssign True precondition assign cleanup
            | src /= dst = (precondition ++ assign, cleanup)
            | otherwise = (precondition, [])
        handleSelfAssign False precondition assign cleanup
            | src /= dst = (assign, cleanup)
            | otherwise = ([], [])

dataLocFor :: BaseType -> State Env (Maybe DataLoc)
dataLocFor t = do
    demotedT <- demoteBaseType t
    useStorage <- inStorage t
    if isPrimitive demotedT then
        pure Nothing
    else if useStorage then
        pure $ Just Storage
    else
        pure $ Just Memory

declareWithLoc :: String -> BaseType -> Maybe DataLoc -> State Env [SolVarDecl]
declareWithLoc x t Nothing = pure <$> (SolVarDecl <$> toSolType t <*> pure x)
declareWithLoc x t (Just loc) = pure <$> (SolVarLocDecl <$> toSolType t <*> pure loc <*> pure x)

declareVar :: String -> BaseType -> State Env [SolVarDecl]
declareVar x t = declareWithLoc x t =<< dataLocFor t

defineVar :: String -> BaseType -> State Env [SolStmt]
defineVar x t = do
    loc <- dataLocFor t
    case loc of
        Just Storage -> do
            decls <- declareVar x t
            concat <$> forM decls (\decl -> do
                (init, setup) <- allocateNew $ varDeclType decl
                pure $ setup ++ [ SolVarDefInit decl init ])

        _ -> map SolVarDef <$> declareVar x t

toSolArg :: VarDef -> State Env [SolVarDecl]
-- TODO: May need to generate multiple var decls per vardef b/c of Solidity (numerous) shortcomings regarding structs
toSolArg (x,(_,t)) = declareVar x t

varDeclType :: SolVarDecl -> SolType
varDeclType (SolVarDecl t _) = t
varDeclType (SolVarLocDecl t _ _) = t

isPrimitiveExpr :: SolExpr -> Bool
isPrimitiveExpr (SolInt _) = True
isPrimitiveExpr (SolBool _) = True
isPrimitiveExpr (SolStr _) = True
isPrimitiveExpr (SolAddr _) = True
isPrimitiveExpr _ = False

toSolType :: BaseType -> State Env SolType
toSolType Nat = pure $ SolTypeName "uint"
toSolType PsaBool = pure $ SolTypeName "bool"
toSolType PsaString = pure $ SolTypeName "string"
toSolType Address = pure $ SolTypeName "address"
toSolType (Table [] (_, t)) = SolArray <$> toSolType t
toSolType ty@(Table (k:ks) t) = do
    defineStruct (encodeBaseType ty) ty
    pure $ SolTypeName $ encodeBaseType ty
toSolType ty@(Record keys fields) = do
    defineStruct (encodeBaseType ty) ty
    pure $ SolTypeName $ encodeBaseType ty
toSolType (Named t) = do
    demotedT <- demoteBaseType (Named t)
    if isPrimitive demotedT then
        toSolType demotedT
    else
        pure $ SolTypeName t

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

inStorage :: BaseType -> State Env Bool
inStorage (Table _ _) = pure True
inStorage (Record _ fields) = or <$> mapM (\(_,(_,t)) -> inStorage t) fields
inStorage (Named t) = do
    typeDecl <- lookupTypeDecl t
    case typeDecl of
        TypeDecl _ _ baseT -> inStorage baseT
inStorage _ = pure False

