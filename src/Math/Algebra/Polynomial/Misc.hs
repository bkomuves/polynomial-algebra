
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
-- * Basic number theory

moebiusMu :: Num c => Int -> c
moebiusMu n 
  | any (>1) expos       =  0
  | even (length primes) =  1
  | otherwise            = -1
  where
    factors = groupIntegerFactors $ integerFactorsTrialDivision (fromIntegral n)
    (primes,expos) = unzip factors

divisors :: Int -> [Int]
divisors n = [ f tup | tup <- tuples' expos ] where
  grps = groupIntegerFactors $ integerFactorsTrialDivision $ fromIntegral n
  (primes,expos) = unzip grps
  int_ps = map fromInteger primes :: [Int]
  f es = foldl' (*) 1 $ zipWith (^) int_ps es

-- | Square-free divisors together with their Mobius mu value
squareFreeDivisors :: Int -> [(Int,Sign)]
squareFreeDivisors n = map f (sublists int_ps) where
  grps = groupIntegerFactors $ integerFactorsTrialDivision $ fromIntegral n
  primes = map fst grps
  int_ps = map fromInteger primes :: [Int]
  f ps = ( foldl' (*) 1 ps , if even (length ps) then Plus else Minus)

-- | List of primes, using tree merge with wheel. Code by Will Ness.
primes :: [Integer]
primes = 2:3:5:7: gaps 11 wheel (fold3t $ roll 11 wheel primes') where                                                             

  primes' = 11: gaps 13 (tail wheel) (fold3t $ roll 11 wheel primes')
  fold3t ((x:xs): ~(ys:zs:t)) 
    = x : union xs (union ys zs) `union` fold3t (pairs t)            
  pairs ((x:xs):ys:t) = (x : union xs ys) : pairs t 
  wheel = 2:4:2:4:6:2:6:4:2:4:6:6:2:6:4:2:6:4:6:8:4:2:4:2:  
          4:8:6:4:6:2:4:6:2:6:6:4:2:4:6:2:6:4:2:4:2:10:2:10:wheel 
  gaps k ws@(w:t) cs@ ~(c:u) 
    | k==c  = gaps (k+w) t u              
    | True  = k : gaps (k+w) t cs  
  roll k ws@(w:t) ps@ ~(p:u) 
    | k==p  = scanl (\c d->c+p*d) (p*p) ws : roll (k+w) t u              
    | True  = roll (k+w) t ps   

  minus xxs@(x:xs) yys@(y:ys) = case compare x y of 
    LT -> x : minus xs  yys
    EQ ->     minus xs  ys 
    GT ->     minus xxs ys
  minus xs [] = xs
  minus [] _  = []
  
  union xxs@(x:xs) yys@(y:ys) = case compare x y of 
    LT -> x : union xs  yys
    EQ -> x : union xs  ys 
    GT -> y : union xxs ys
  union xs [] = xs
  union [] ys =ys

--------------------------------------------------------------------------------
-- Prime factorization

-- | Groups integer factors. Example: from [2,2,2,3,3,5] we produce [(2,3),(3,2),(5,1)]  
groupIntegerFactors :: [Integer] -> [(Integer,Int)]
groupIntegerFactors = map f . group . sort where
  f xs = (head xs, length xs)

-- | The naive trial division algorithm.
integerFactorsTrialDivision :: Integer -> [Integer]
integerFactorsTrialDivision n 
  | n<1 = error "integerFactorsTrialDivision: n should be at least 1"
  | otherwise = go primes n 
  where
    go _  1 = []
    go rs k = sub ps k where
      sub [] k = [k]
      sub qqs@(q:qs) k = case mod k q of
        0 -> q : go qqs (div k q)
        _ -> sub qs k
      ps = takeWhile (\p -> p*p <= k) rs  

--------------------------------------------------------------------------------
-- * Basic combinatorics

tuples' :: [Int] -> [[Int]]
tuples' [] = [[]]
tuples' (s:ss) = [ x:xs | x <- [0..s] , xs <- tuples' ss ] 

-- | All sublists of a list.
sublists :: [a] -> [[a]]
sublists [] = [[]]
sublists (x:xs) = sublists xs ++ map (x:) (sublists xs)  

--------------------------------------------------------------------------------

