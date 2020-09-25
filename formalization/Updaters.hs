{-# LANGUAGE ScopedTypeVariables #-}

data BaseType = Nat
              | Table [String] [(String, Type)]
    deriving (Show, Eq)

data TyQuant = Empty | Nonempty | Any | One | Every
    deriving (Show, Eq)

data Locator = Var String
             | Field Locator String
             | NewTable [String] [Locator]
             | Filter Locator TyQuant -- In the real thing, we also have some predicate, but that doesn't matter for the purposes of creating the updaters.
    deriving (Show, Eq)

type Type = (TyQuant, BaseType)
type Env = String -> Type

join :: TyQuant -> TyQuant -> TyQuant
join _ _ = undefined

-- ASSUMES THAT THE TWO BASE TYPES ARE THE SAME!!!!!
joinTy :: Type -> Type -> Type
joinTy (q1, t) (q2, _) = (join q1 q2, t)

allNat :: Env
allNat = \_ -> (Any, Nat)

withType :: (String, Type) -> Env -> Env
withType (x, t) gamma = \v -> if v == x then t else gamma v

updateField :: String -> (Type -> Type) -> Type -> Type
updateField x f (q, Nat) = undefined
updateField x f (q, Table keys fields) = (q, Table keys $ map (\(fName, fType) -> if fName == x then (fName, f fType) else (fName, fType)) fields)

makeUpdater :: Locator -> (Env -> (Type -> Type) -> Env)
makeUpdater (Var x) gamma f = \v -> if x == v then f (gamma x) else gamma v
makeUpdater (Field loc x) gamma f =
    let u = makeUpdater loc
    in u gamma $ updateField x f
makeUpdater (NewTable keys elements) gamma f =
    let us = map makeUpdater elements
    in foldr (\u delta -> u delta f) gamma us
makeUpdater (Filter loc q) gamma f =
    let u = makeUpdater loc
    in u gamma $ if q == Empty then id
                 else if q == Every then f
                 else
                    \t -> joinTy t (f t) -- Because we can't be sure whether it will be selected or not

-- makeUpdater (Field (Var "m") "value") (withType ("m", (Any, Table ["key"] [("key", (One, Nat)), ("value", (One, Nat))])) allNat) (\(q, t) -> (Empty, t)) "m"
-- == (Any,Table ["key"] [("key",(One,Nat)),("value",(Empty,Nat))])
--
-- makeUpdater (NewTable [] [Var "x", Field (Var "y") "key"]) (withType ("y", (Any, Table [] [("key", (One, Nat)), ("value", (One, Nat))])) allNat) (\(q, t) -> (Empty, t)) "y"
-- == (Any,Table [] [("key",(Empty,Nat)),("value",(One,Nat))])

