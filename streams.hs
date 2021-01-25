{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

import Control.Applicative
import Control.Monad
import Control.Monad.Identity

import Data.Functor.Compose
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Ord

import Debug.Trace

sublist :: Eq a => [a] -> [a] -> Bool
sublist [] _ = True
sublist (x:xs) ys = x `elem` ys && sublist xs (ys \\ [x])

selectBySnd :: Eq b => b -> [(a,b)] -> ([(a,b)], [(a,b)])
selectBySnd x [] = ([], [])
selectBySnd x ((a,b):rest)
    | x == b = (rest, [(a,b)])
    | otherwise =
        let (res, sel) = selectBySnd x rest
        in ((a,b) : res, sel)

selectManyBySnd :: Eq b => [b] -> [(a,b)] -> ([(a,b)], [(a,b)])
selectManyBySnd [] leftover = (leftover, [])
selectManyBySnd (x:xs) ys =
    let (rest, sel) = selectBySnd x ys
        (leftover, taken) = selectManyBySnd xs rest
    in (leftover, sel ++ taken)

groupWith :: Eq k => (k -> [a] -> [b] -> (k, c)) -> [(k,a)] -> [(k,b)] -> ([(k,a)], [(k,b)], [(k,c)])
groupWith f [] ys = ([], ys, [])
groupWith f xs [] = (xs, [], [])
groupWith f ((k,a):xs) ys =
    let (takenXs, leftXs) = partition ((== k) . fst) xs
        (takenYs, leftYs) = partition ((== k) . fst) ys
        (leftFst, leftSnd, transformed) = groupWith f leftXs leftYs
    in (leftFst, leftSnd, f k (a : map snd takenXs) (map snd takenYs) : transformed)

splitWith :: (Monoid b, Monoid c) => (a -> (b,c)) -> [a] -> (b, c)
splitWith f xs = mconcat $ map f xs

fromNat :: Int -> [()]
fromNat n = replicate n ()

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

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

-- flow :: a -> Locator a c -> Locator a c -> a
flow state src@Locator{} dst@Locator{} =
    let (newState, selected) = runLocator [state] src
        ([finalState], []) = runDestination newState (dst |> combine selected)
    in finalState

-- test :: [Locator a b] -> Locator [a] [b]

selectVals :: (Show a, Monoid a, Eq a) => [a] -> Locator [a] [a]
selectVals toTake = Locator $ \lists f ->
    let run [] lists = Just [(lists, mempty)]
        run leftToTake [] = Nothing
        run leftToTake ((k,vals):rest) =
            let taken = vals \\ (vals \\ leftToTake)
                tailRes = run (leftToTake \\ taken) rest in
            if taken == [] then
                (:) <$> pure ([(k,vals)], mempty) <*> tailRes
            else
                let (ret, sel) = f [(k, taken)]
                    (xs, ys, grouped) = groupWith (\k xs ys -> (k, concat $ xs ++ ys)) [(k, vals \\ taken)] ret
                in (:) <$> pure (xs ++ ys ++ grouped, sel) <*> tailRes
    in case run toTake lists of
        Nothing -> ([], mempty)
        Just results ->
            let (rets, sels) = splitWith (\(a,b) -> ([a],[b])) results
            in (concat rets, mconcat sels)

selectFst :: (Show a, Show b, Monoid a, Monoid b, Eq a) => Locator (a,b) a
selectFst = Locator $ \vals f ->
    let (fsts, snds) = splitWith (\(k,(a,b)) -> ([(k,a)], [(k,b)])) vals
        (ret, sel) = f fsts
        (xs, ys, grouped) = groupWith (\k xs ys -> (k, mconcat (map (,mempty) xs) <> mconcat (map (mempty,) ys))) ret snds
    in (map (\(k,b) -> (k, (mempty,b))) ys ++ grouped, sel)

selectSnd :: (Monoid a, Monoid b, Eq a) => Locator (a,b) b
selectSnd = Locator $ \vals f ->
    let (ret, sel) = f [ (k,b) | (k,(a,b)) <- vals ]
        (xs, ys, grouped) = groupWith (\k xs ys -> (k, mconcat (map (mempty,) xs) <> mconcat ys)) ret [ (k, (a,mempty)) | (k,(a,b)) <- vals]
    in (ys ++ grouped, sel)

headOr :: a -> [a] -> a
headOr x [] = x
headOr _ (y:_) = y

eachK :: Monoid b => (forall kb. Fresh kb => [(kb,[b])] -> ([(kb,[b])], r)) -> (forall kb. Fresh kb => [(kb,b)] -> ([(kb,b)], r))
eachK g transformed =
    let (ret, sel) = g $ map (\(k,b) -> (k, [b])) transformed
    in (map (\(k,bs) -> (k, headOr mempty bs)) ret, sel)

-- TODO: This should probably work with any functions f :: a -> c and g :: c -> a s.t. g . f = id (then this is just f = \x -> [x] and g = head)
each :: (Show a, Show b) => Locator a b -> Locator [a] [b]
each (Locator f) = Locator $ \lists g ->
    let temp = concatMap (\(k,vals) -> zipWith (\i v -> ((i,k), v)) ([0..] :: [Integer]) vals) lists
        temp2 = concatMap (\(k,vals) -> zipWith (\i v -> (k, (i,mempty))) ([0..] :: [Integer]) vals) lists
        (ret, sel) = f temp $ \transformed -> eachK g transformed
        (finalXs, finalYs, finalGrouped) = groupWith (\k xs ys -> let (xs', ys', grouped') = groupWith (\i xs' ys' -> (i, mconcat $ xs' ++ ys')) xs ys in (k, xs' ++ ys' ++ grouped')) temp2 $ map (\((i,k),v) -> (k,(i,v))) ret
        go (k, (i,v)) = (k, [v])
        go' (k, v) = (k, map snd v)
    in (map go finalXs ++ map go finalYs ++ map go' finalGrouped, sel)

constructList :: (Show a, Eq a, Monoid a) => Locator a [a]
constructList = preConstructList |> each selectSnd

preConstructList :: (Show a, Eq a, Monoid a) => Locator a [(Sum Integer, a)]
preConstructList = Locator $ \vals f ->
    let indexed = zipWith (\i (_,a) -> (i,a)) [0..] vals
        (ret, sel) = f [(0 :: Sum Integer, indexed)]
        keyIndexed = zipWith (\i (k,a) -> (i,(k,a))) [0..] vals
        (xs,ys,grouped) = groupWith (\idx xs ys -> (idx, (fst (head ys), mconcat xs))) (concatMap snd ret) keyIndexed
    in (map snd ys ++ map snd grouped, sel)

selectList :: Eq a => [a] -> [a] -> ([a], [a])
selectList xs ys = (xs \\ ys, ys \\ xs)

selectUnit :: () -> () -> ((), ())
selectUnit a b = ((), ())

summation :: (Eq a, Monoid a) => (a -> a -> (a, a)) -> Locator [a] a
summation select = Locator $ \vals f ->
    let (ret, sel) = f $ map (\(k,v) -> (k, mconcat v)) vals
        -- redistributed = groupWith (\k x y -> (k, mconcat $ x <> y)) $ redistribute vals $ map snd ret
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

combine :: Monoid a => [a] -> Locator a a
combine vals = Locator $ \rest k ->
    case k rest of
        (ret, sel) -> (zipWith (\(k,a) b -> (k, a <> b)) ret vals, sel)

