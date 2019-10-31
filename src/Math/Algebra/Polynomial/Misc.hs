
-- | Some auxilary functions

{-# LANGUAGE CPP, BangPatterns, TypeSynonymInstances, FlexibleInstances, DeriveFunctor #-}
module Math.Algebra.Polynomial.Misc where

--------------------------------------------------------------------------------

import Data.List
import Data.Monoid
import Data.Ratio

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)     
import Data.Foldable
import Data.Semigroup
#endif

import Control.Monad

import qualified Data.Map.Strict as Map ; import Data.Map (Map)

--------------------------------------------------------------------------------

{-
-- * Pairs

data Pair a 
  = Pair a a 
  deriving (Eq,Ord,Show,Functor)
-}

--------------------------------------------------------------------------------

equating :: Eq b => (a -> b) -> a -> a -> Bool  
equating f x y = (f x == f y)

--------------------------------------------------------------------------------
-- * Lists

unique :: Ord a => [a] -> [a]
unique = map head . group . sort

-- | Synonym for histogram
count :: Ord b => [b] -> Map b Integer
count = histogram

histogram :: Ord b => [b] -> Map b Integer
histogram xs = foldl' f Map.empty xs where
  f old x = Map.insertWith (+) x 1 old

{-# SPECIALIZE sum' :: [Int]     -> Int     #-}
{-# SPECIALIZE sum' :: [Integer] -> Integer #-}
sum' :: Num a => [a] -> a
sum' = foldl' (+) 0

longZipWith :: (a -> c) -> (b -> c) -> (a -> b -> c) -> [a] -> [b] -> [c]
longZipWith f g h = go where
  go (x:xs) (y:ys) = h x y : go xs ys
  go xs     []     = map f xs
  go []     ys     = map g ys

--------------------------------------------------------------------------------
-- * Maps
  
deleteLookup :: Ord a => a -> Map a b -> (Maybe b, Map a b)
deleteLookup k table = (Map.lookup k table, Map.delete k table)  

unsafeDeleteLookup :: Ord a => a -> Map a b -> (b, Map a b)
unsafeDeleteLookup k table = (fromJust (Map.lookup k table), Map.delete k table) where
  fromJust mb = case mb of
    Just y  -> y
    Nothing -> error "unsafeDeleteLookup: key not found"

-- | Example usage: @insertMap (:[]) (:) ...@
insertMap :: Ord k => (b -> a) -> (b -> a -> a) -> k -> b -> Map k a -> Map k a
insertMap f g k y = Map.alter h k where
  h mb = case mb of
    Nothing -> Just (f y)
    Just x  -> Just (g y x)    

-- | Example usage: @buildMap (:[]) (:) ...@
buildMap :: Ord k => (b -> a) -> (b -> a -> a) -> [(k,b)] -> Map k a
buildMap f g xs = foldl' worker Map.empty xs where
  worker !old (k,y) = Map.alter h k old where
    h mb = case mb of
      Nothing -> Just (f y)
      Just x  -> Just (g y x)    

--------------------------------------------------------------------------------
-- * Signs

data Sign
  = Plus                            -- hmm, this way @Plus < Minus@, not sure about that
  | Minus
  deriving (Eq,Ord,Show,Read)

oppositeSign :: Sign -> Sign
oppositeSign s = case s of
  Plus  -> Minus
  Minus -> Plus

mulSign :: Sign -> Sign -> Sign
mulSign s1 s2 = case s1 of
  Plus  -> s2
  Minus -> oppositeSign s2

productOfSigns :: [Sign] -> Sign
productOfSigns = go Plus where
  go !acc []     = acc
  go !acc (x:xs) = case x of
    Plus  -> go acc xs
    Minus -> go (oppositeSign acc) xs

--------------------------------------------------------------------------------

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)        

instance Semigroup Sign where
  (<>)    = mulSign
  sconcat = foldl1 mulSign

instance Monoid Sign where
  mempty  = Plus
  mconcat = productOfSigns

#else

instance Monoid Sign where
  mempty  = Plus
  mappend = mulSign
  mconcat = productOfSigns

#endif

--------------------------------------------------------------------------------

{-# SPECIALIZE signValue :: Sign -> Int     #-}
{-# SPECIALIZE signValue :: Sign -> Integer #-}

-- | @+1@ or @-1@
signValue :: Num a => Sign -> a
signValue s = case s of
  Plus  ->  1
  Minus -> -1

{-# SPECIALIZE signed :: Sign -> Int     -> Int     #-}
{-# SPECIALIZE signed :: Sign -> Integer -> Integer #-}

-- | Negate the second argument if the first is 'Minus'
signed :: Num a => Sign -> a -> a
signed s y = case s of
  Plus  -> y
  Minus -> negate y

class IsSigned a where
  signOf :: a -> Maybe Sign

signOfNum :: (Ord a, Num a) => a -> Maybe Sign 
signOfNum x = case compare x 0 of
  LT -> Just Minus
  GT -> Just Plus
  EQ -> Nothing

instance IsSigned Int      where signOf = signOfNum
instance IsSigned Integer  where signOf = signOfNum
instance IsSigned Rational where signOf = signOfNum

--------------------------------------------------------------------------------
-- * Numbers

fromRat :: Rational -> Integer
fromRat r = case denominator r of
  1 -> numerator r
  _ -> error "fromRat: not an integer"    

safeDiv :: Integer -> Integer -> Integer
safeDiv a b = case divMod a b of
  (q,0) -> q
  (q,r) -> error $ "saveDiv: " ++ show a ++ " = " ++ show b ++ " * " ++ show q ++ " + " ++ show r

--------------------------------------------------------------------------------
