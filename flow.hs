{-# LANGUAGE GADTs #-}

import Data.List
import Data.Maybe

class Monad r => Resource r where
    empty :: Eq a => r a

    -- NOTE: combine and split only need to be well-behaved when canContain or contains (respectively) return True
    combine :: Eq a => r a -> r a -> r a
    split :: Eq a => r a -> r a -> r a

    contains :: Eq a => r a -> r a -> Bool
    canContain :: Eq a => r a -> r a -> Bool
    convert :: (Eq a, Resource s) => r a -> s a

select :: Eq a => a -> [a] -> Maybe [a]
select _ [] = Nothing
select x (y:ys)
    | x == y = Just ys
    | otherwise = (:) <$> pure y <*> select x ys

instance Resource [] where
    empty = []
    combine = (++)
    xs `split` selected = foldr (\a b -> fromMaybe [] (select a b)) selected xs
    xs `contains` [] = True
    xs `contains` (y:ys) = isJust $ do
        rest <- select y xs
        pure $ rest `contains` ys

    canContain _ _ = True

    convert xs = foldr (combine . pure) empty xs

newtype Set a = Set { vals :: [a] }
    deriving Show

symDif :: Eq a => Set a -> Set a -> Set a
(Set xs) `symDif` (Set ys) = Set $ nub $ (nub xs \\ nub ys) ++ (nub ys \\ nub xs)

instance Eq a => Eq (Set a) where
    a == b = null $ vals $ a `symDif` b

instance Functor Set where
    fmap f (Set xs) = Set $ fmap f xs

instance Applicative Set where
    pure = Set . pure
    (Set fs) <*> (Set xs) = Set [ f x | f <- fs, x <- xs ]

setUnion (Set xs) = foldr (\(Set xs) (Set ys) -> Set $ xs ++ ys) (Set []) xs

instance Monad Set where
    (Set xs) >>= f = setUnion $ Set $ f <$> xs

instance Resource Set where
    empty = Set []
    combine a b = setUnion $ Set [a,b]
    (Set xs) `split` (Set ys) = Set $ nub $ (nub xs) \\ (nub ys)
    a `contains` b = empty == b `split` a
    a `canContain` b = b `split` a == b
    convert (Set xs) = foldr (combine . pure) empty $ nub xs

instance Resource Maybe where
    empty = Nothing

    combine Nothing Nothing = Nothing
    combine Nothing (Just b) = Just b
    combine (Just a) Nothing = Just a
    combine (Just a) (Just b) = Just a

    Nothing `split` Nothing = Nothing
    Nothing `split` (Just b) = Nothing
    (Just a) `split` Nothing = Just a
    (Just a) `split` (Just b) = Nothing

    Nothing `canContain` Nothing = True
    Nothing `canContain` (Just b) = True
    (Just a) `canContain` Nothing = True
    (Just a) `canContain` (Just b) = False

    _ `contains` Nothing = True
    Nothing `contains` (Just b) = False
    (Just a) `contains` (Just b) = a == b

    convert Nothing = empty
    convert (Just a) = pure a

compose :: (Eq a, Eq b, Eq c, Resource r, Resource s) => (b -> s c) -> (a -> r b) -> (a -> s c)
compose g f = \a -> convert (f a) >>= g

flow :: (Eq a, Eq b, Resource r, Resource s)
     => r a -> (r a -> r a) -> r (a -> b) -> s b -> Either String (r a, s b)
flow source selector transformer dest =
    let selected = selector source
        sent = convert (transformer <*> selected)
    in if source `contains` selected && dest `canContain` sent then
            Right (source `split` selected, dest `combine` sent)
        else
            Left "Cannot flow!"

type Linking r k v = [(k, r v)]

