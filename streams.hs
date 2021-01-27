{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Identity

import Data.Functor.Compose
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord

import Debug.Trace

findKeyAndRemove :: Eq k => k -> [(k,a)] -> Maybe ((k,a), [(k,a)])
findKeyAndRemove k [] = Nothing
findKeyAndRemove k ((k',a):rest)
    | k == k' = Just ((k', a), rest)
    | otherwise =
        case findKeyAndRemove k rest of
            Nothing -> Nothing
            Just (res, left) -> Just (res, (k',a) : left)

groupSize :: [a] -> [b] -> ([a], [b], [a], [b])
groupSize xs [] = ([], [], xs, [])
groupSize [] ys = ([], [], [], ys)
groupSize (x:xs) (y:ys) =
    let (takenXs, takenYs, leftXs, leftYs) = groupSize xs ys
    in (x : takenXs, y : takenYs, leftXs, leftYs)

groupWith :: Eq k => (k -> [a] -> [b] -> c) -> [(k,a)] -> [(k,b)] -> [c]
groupWith f [] [] = []
groupWith f [] ((k,b):ys) =
    let (takenYs, rest) = partition ((== k) . fst) ys
    in f k [] (b : map snd takenYs) : groupWith f [] rest
groupWith f ((k,a):xs) ys =
    let (takenXs, leftXs) = partition ((== k) . fst) xs
        (takenYs, leftYs) = partition ((== k) . fst) ys
    in case takenYs of
        [] -> f k (a : map snd takenXs) [] : groupWith f leftXs leftYs
        _ -> let (takenXs', takenYs', leftXs', leftYs') = groupSize ((k,a) : takenXs) takenYs
             in f k (map snd takenXs') (map snd takenYs') : groupWith f (leftXs' ++ leftXs) (leftYs' ++ leftYs)

label :: [a] -> [(Sum Integer, a)]
label = zip [0..]

---------------------------------------------------------
--- These exist so that we can reduce how many auxiliary functions we need in the language
--- They're all based on map/ifEmpty
---------------------------------------------------------
splitWith :: (Monoid b, Monoid c) => (a -> (b,c)) -> [a] -> (b, c)
splitWith f xs = mconcat $ map f xs

myMap :: Eq a => (a -> b) -> [a] -> [b]
myMap f xs = groupWith (\k a b -> f (head a)) (label xs) []

ifEmpty :: [a] -> b -> b -> b
ifEmpty [] e1 e2 = e1
ifEmpty xs e1 e2 = e2

headOr x xs = ifEmpty xs x (head xs)
---------------------------------------------------------
--- End
---------------------------------------------------------

fromNat :: Int -> [()]
fromNat n = replicate n ()

data Val = Nat Integer | Boolean Bool | Multiset [Val] | Empty | Pair (Val, Val)
    deriving (Show, Eq)

instance Semigroup Val where
    Nat n <> Nat m = Nat $ n + m
    Boolean b1 <> Boolean b2 = Boolean $ b1 || b2
    Multiset m1 <> Multiset m2 = Multiset $ m1 ++ m2
    Pair p1 <> Pair p2 = Pair $ p1 <> p2

    Empty <> b = b
    a <> Empty = a

instance Monoid Val where
    mempty = Empty

class Monoid a => Value a where
    toVal :: a -> Val
    fromVal :: Val -> a

instance Value Val where
    toVal = id
    fromVal = id

instance Value () where
    toVal () = Nat 1
    fromVal _ = ()

instance Value Any where
    toVal (Any b) = Boolean b
    fromVal (Boolean b) = Any b

instance (Value a, Value b) => Value (a,b) where
    toVal (a, b) = Pair (toVal a, toVal b)
    fromVal (Pair (a, b)) = (fromVal a, fromVal b)

instance Value [()] where
    toVal xs = Nat $ genericLength xs
    fromVal (Multiset xs) = replicate (length xs) ()

instance (Value a, Value b) => Value [(a,b)] where
    toVal xs = Multiset $ map toVal xs
    fromVal (Multiset m) = map fromVal m

instance Value [a] => Value [[a]] where
    toVal xs = Multiset $ map toVal xs
    fromVal (Multiset m) = map fromVal m

class (Show k, Eq k) => Fresh k where
    fresh :: [k] -> k

    freshes :: [k] -> [k]
    freshes xs = let new = fresh xs in new : freshes (new : xs)

instance Fresh Integer where
    fresh [] = 0
    fresh xs = maximum xs + 1

instance Fresh (Sum Integer) where
    fresh [] = 0
    fresh xs = maximum xs + 1

instance Enum (Sum Integer) where
    toEnum = Sum . toEnum
    fromEnum = fromEnum . getSum

instance (Fresh a, Fresh b) => Fresh (a, b) where
    fresh xs = (fresh (map fst xs), fresh (map snd xs))

-- TODO: Replace Monoid by Resource
-- TODO: If we can make this abstraction a bit nicer, maybe more progress can be made...
data Locator a b where
    Locator :: (Monoid a, Monoid b)
                => (forall ka r. (Fresh ka, Monoid r) => [(ka,a)] -> (forall kb. Fresh kb => [(kb,b)] -> ([(kb,b)], r)) -> ([(ka,a)],r))
                -> Locator a b

-- runLocator [(fromNat 9, fromNat 17), (fromNat 10, fromNat 2)] $ constructList |> each selectFst |> selectVals2 [fromNat 9]
-- runLocator [(fromNat 9, fromNat 0)] $ selectFst |> each (selectVals (fromNat 5)) |> summation selectUnit
-- runLocator [(fromNat 9, fromNat 3), (fromNat 2, fromNat 6)] $ constructList |> each selectFst |> selectVals2 [fromNat 9] |> each (each (selectVals (fromNat 5)))
runLocator :: [a] -> Locator a b -> ([a], [b])
runLocator vals (Locator f) =
    let (taggedRet, sel) = f (zip ([0..] :: [Integer]) vals) $ \taggedVals -> ([], map snd taggedVals)
    in (map snd taggedRet, sel)

runDestination :: [a] -> Locator a b -> ([a], [b])
runDestination vals (Locator f) =
    let (taggedRet, sel) = f (zip ([0..] :: [Integer]) vals) $ \taggedVals -> (taggedVals, [])
    in (map snd taggedRet, sel)

(|>) :: Locator a b -> Locator b c -> Locator a c
(Locator f) |> (Locator g) = Locator $ \vals k ->
    f vals $ \taggedVals -> g taggedVals $ \finalVals -> k finalVals

-- flow (fromNat 9, fromNat 0) (selectFst |> each (selectVals (fromNat 5))) selectSnd
-- flow :: a -> Locator a c -> Locator a c -> a
flow state src@Locator{} dst@Locator{} =
    let (newState, selected) = runLocator [state] src
        ([finalState], []) = runDestination newState (dst |> combine selected)
    in finalState


-- Some more "combinator-y" locators
splitLoc :: Locator a b -> Locator a c -> Locator a (b,c)
selectVals3 :: Locator (a,a) a
filter :: Locator a a
-- Others
singleton :: Locator a [a]
formList :: Locator (a,a) [a]

selectVals :: (Show a, Monoid a, Eq a) => [a] -> Locator a a
selectVals toTake = Locator $ \vals f ->
    let temp = groupWith (\k xs ys -> (k, ifEmpty xs [] ys)) (map (,()) toTake) $ map (\(k,a) -> (a,k)) vals
        taken = mconcat $ map (\(a, ks) -> map (,a) ks) temp
        leftover = vals \\ taken
        (ret, sel) = f taken
        finalRet = groupWith (\k x y -> (k, mconcat $ x <> y)) leftover ret
    in if length taken /= length toTake then
        ([], mempty)
       else
        (finalRet, sel)

selectVals2 :: (Show a, Monoid a, Eq a) => [a] -> Locator [a] [a]
selectVals2 toTake = Locator $ \lists f ->
    let run [] lists = Just [(lists, mempty)]
        run leftToTake [] = Nothing
        run leftToTake ((k,vals):rest) =
            let taken = vals \\ (vals \\ leftToTake)
                tailRes = run (leftToTake \\ taken) rest in
            if taken == [] then
                (:) <$> pure ([(k,vals)], mempty) <*> tailRes
            else
                let (ret, sel) = f [(k, taken)]
                    grouped = groupWith (\k xs ys -> (k, concat $ xs ++ ys)) [(k, vals \\ taken)] ret
                in (:) <$> pure (grouped, sel) <*> tailRes
    in case run toTake lists of
        Nothing -> ([], mempty)
        Just results ->
            let (rets, sels) = splitWith (\(a,b) -> ([a],[b])) results
            in (concat rets, mconcat sels)

selectFst :: (Show a, Show b, Monoid a, Monoid b, Eq a) => Locator (a,b) a
selectFst = Locator $ \vals f ->
    let (fsts, snds) = splitWith (\(k,(a,b)) -> ([(k,a)], [(k,b)])) vals
        (ret, sel) = f fsts
        grouped = groupWith (\k xs ys -> (k, (mconcat xs, mconcat ys))) ret snds
    in (grouped, sel)

selectSnd :: (Monoid a, Monoid b, Eq a) => Locator (a,b) b
selectSnd = Locator $ \vals f ->
    let (fsts, snds) = splitWith (\(k,(a,b)) -> ([(k,a)], [(k,b)])) vals
        (ret, sel) = f snds
        grouped = groupWith (\k xs ys -> (k, (mconcat xs, mconcat ys))) fsts ret
    in (grouped, sel)

eachK :: Monoid b => (forall kb. Fresh kb => [(kb,[b])] -> ([(kb,[b])], r)) -> (forall kb. Fresh kb => [(kb,b)] -> ([(kb,b)], r))
eachK g transformed =
    let (ret, sel) = g $ map (\(k,b) -> (k, [b])) transformed
    in (map (\(k,bs) -> (k, headOr mempty bs)) ret, sel)

-- TODO: This should probably work with any functions f :: a -> c and g :: c -> a s.t. g . f = id (then this is just f = \x -> [x] and g = head)
each :: (Show a, Show b) => Locator a b -> Locator [a] [b]
each (Locator f) = Locator $ \lists g ->
    let temp = mconcat $ map (\(k,vals) -> map (\(i,v) -> ((i,k),v)) $ label vals) lists
        (ret, sel) = f temp $ \transformed -> eachK g transformed
        temp3 = groupWith (\k xs ys -> (k, groupWith (\i xs' ys' -> (i, mconcat ys')) xs ys)) [] $ map (\((i,k),v) -> (k,(i,v))) ret
        finalGrouped = groupWith (\k _ ys -> (k, mconcat ys)) [] $ map (\(k,vs) -> (k, map snd vs)) temp3
    in (finalGrouped, sel)

constructList :: (Show a, Eq a, Monoid a) => Locator a [a]
constructList = preConstructList |> each selectSnd

preConstructList :: (Show a, Eq a, Monoid a) => Locator a [(Sum Integer, a)]
preConstructList = Locator $ \vals f ->
    let (indexed, keyIndexed) = unzip $ map (\(i,(k,a)) -> ((i,a),(i,k))) $ label vals
        (ret, sel) = f $ label [indexed]
        grouped = groupWith (\idx xs ys -> (idx, (head ys, mconcat xs))) (mconcat $ map snd ret) keyIndexed
    in (map snd grouped, sel)

combine :: (Show a, Monoid a) => [a] -> Locator a a
combine vals = Locator $ \rest k ->
    let (ret, sel) = k rest
    in case ret of
        [(k,v)] -> ([(k, v <> mconcat vals)], sel)
        _ -> ([], mempty) -- TODO: REPLACE THIS WITH A FAILURE!

selectList :: Eq a => [a] -> [a] -> ([a], [a])
selectList xs ys = (xs \\ ys, ys \\ xs)

selectUnit :: () -> () -> ((), ())
selectUnit a b = ((), ())

summation :: (Eq a, Monoid a) => (a -> a -> (a, a)) -> Locator [a] a
summation select = Locator $ \vals f ->
    let (ret, sel) = f $ map (\(k,v) -> (k, mconcat v)) vals
        redistribute _ [] = []
        redistribute [] _ = []
        redistribute ((k,vals):rest) (x:xs) =
            let (leftoverX, leftoverVals, filled) = fill vals x
            in if leftoverX == mempty then
                (k,filled) : redistribute ((k,leftoverVals):rest) xs
               else
                (k,filled) : redistribute rest (leftoverX:xs)

        fill [] x = (x, [], [])
        fill (y:ys) x =
            let (newY, selected) = select y x
                (newX, taken) = select x y in
            if newY == mempty then
                if newX == mempty then (mempty, ys, [y])
                else
                    let (leftoverX, leftoverVals, filled) = fill ys newX
                    in (leftoverX, leftoverVals, y : filled)
            else
                if newX == mempty then (mempty, newY:ys, [selected])
                else
                    let (leftoverX, leftoverVals, filled) = fill ys newX
                    in (leftoverX, newY : leftoverVals, selected : filled)
    in (redistribute vals $ map snd ret, sel)

