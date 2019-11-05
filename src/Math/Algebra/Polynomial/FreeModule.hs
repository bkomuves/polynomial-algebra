
-- | Free modules over some generator set.  
--
-- This module should be imported qualified.

{-# LANGUAGE 
      BangPatterns, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, TypeFamilies,
      ConstraintKinds, KindSignatures
  #-}
module Math.Algebra.Polynomial.FreeModule where

--------------------------------------------------------------------------------

import Prelude   hiding ( sum , product )
import Data.List hiding ( sum , product )

import Data.Monoid
import Data.Ratio
import Data.Maybe

import Data.Typeable
import Data.Proxy

import Control.Monad ( foldM )

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Data.Set (Set)

--------------------------------------------------------------------------------
-- * Partial monoids

class PartialMonoid a where
  pmUnit :: a
  pmAdd  :: a -> a -> Maybe a
  pmSum  :: [a] -> Maybe a

  pmSum xs  = case xs of { [] -> Just pmUnit ; (y:ys) -> foldM pmAdd y ys }
  pmAdd x y = pmSum [x,y]

{- undecidable instance
instance Monoid a => PartialMonoid a where
  pmUnit    = mempty
  pmAdd x y = Just $ mappend x y
  pmSum xs  = Just $ mconcat xs
-}

--------------------------------------------------------------------------------
-- * A type class

-- | The reason for this type class is to make using newtype wrappers more convenient
class (Ord (BaseF a)) => FreeModule a where
  type BaseF  a :: *
  type CoeffF a :: *
  toFreeModule   :: a -> FreeMod (CoeffF a) (BaseF a)
  fromFreeModule :: FreeMod (CoeffF a) (BaseF a) -> a
  
instance Ord b => FreeModule (FreeMod c b) where
  type BaseF  (FreeMod c b) = b
  type CoeffF (FreeMod c b) = c
  toFreeModule   = id
  fromFreeModule = id

--------------------------------------------------------------------------------
-- * Free modules

-- | Free module over a coefficient ring with the given base. Internally a map
-- storing the coefficients. We maintain the invariant that the coefficients
-- are never zero.
newtype FreeMod coeff base = FreeMod { unFreeMod :: Map base coeff } deriving (Eq,Ord,Show)

-- | Free module with integer coefficients
type ZMod base = FreeMod Integer base

-- | Free module with rational coefficients
type QMod base = FreeMod Rational base

--------------------------------------------------------------------------------
-- * Support

-- | Number of terms
size :: FreeMod c b -> Int
size (FreeMod table) = Map.size table

-- | The support as a list
supportList :: Ord b => FreeMod c b -> [b] 
supportList (FreeMod table) = Map.keys table

-- | The support as a set
supportSet :: Ord b => FreeMod c b -> Set b 
supportSet (FreeMod table) = Map.keysSet table

--------------------------------------------------------------------------------

instance (Monoid b, Ord b, Eq c, Num c) => Num (FreeMod c b) where
  (+)    = add
  (-)    = sub
  negate = neg
  (*)    = mul
  fromInteger = konst . fromInteger
  abs      = id       -- error "FreeMod/abs"
  signum _ = konst 1  -- error "FreeMod/signum"

--------------------------------------------------------------------------------
-- * Sanity checking

-- | Should be the identity function
normalize :: (Ord b, Eq c, Num c) => FreeMod c b -> FreeMod c b
normalize = FreeMod . Map.filter (/=0) . unFreeMod

-- | Safe equality testing (should be identical to @==@)
safeEq :: (Ord b, Eq b, Eq c, Num c) => FreeMod c b -> FreeMod c b -> Bool
safeEq x y = normalize x == normalize y

--------------------------------------------------------------------------------
-- * Constructing and deconstructing

-- | The additive unit
zero :: FreeMod c b
zero = FreeMod $ Map.empty

-- | Testing for equality with zero 
-- (WARNING: this assumes that the invariant of never having zero coefficients actually holds!)
isZero :: Ord b => FreeMod c b -> Bool
isZero (FreeMod mp) = Map.null mp

-- | A module generator
generator :: Num c => b -> FreeMod c b 
generator x = FreeMod $ Map.singleton x 1

-- | A single generator with a coefficient
singleton :: (Ord b, Num c, Eq c) => b -> c -> FreeMod c b
singleton b c = FreeMod $ if c/=0
  then Map.singleton b c
  else Map.empty

-- | Conversion from list. 
-- This should handle repeated generators correctly (adding their coefficients).
fromList :: (Eq c, Num c, Ord b) => [(b,c)] -> FreeMod c b
fromList = FreeMod . Map.filter cond . Map.fromListWith (+) where
  cond x = (x /= 0)

fromMap :: (Eq c, Num c, Ord b) => Map b c -> FreeMod c b
fromMap = FreeMod . Map.filter (/=0) 

-- | Returns the sum of the given generator elements
fromGeneratorSet :: (Ord b, Num c) => Set b -> FreeMod c b
fromGeneratorSet = FreeMod . Map.fromSet (const 1)

-- | Returns the sum of the given generator elements 
fromGeneratorList :: (Ord b, Eq c, Num c) => [b] -> FreeMod c b
fromGeneratorList bs = FreeMod $ foldl' f Map.empty bs where
  f !old !b = Map.alter g b old
  g !mb     = case mb of
    Nothing   -> Just 1
    Just k    -> let k' = k+1                                  -- when for example working in a finite field
                 in  if k' /= 0 then Just k' else Nothing      -- repeated adding of 1 can result in zero...

-- | Conversion to list 
toList :: FreeMod c b -> [(b,c)]
toList = Map.toList . unFreeMod

-- | Extract the coefficient of a generator
coeffOf :: (Ord b, Num c) => b -> FreeMod c b -> c
coeffOf b (FreeMod x) = case Map.lookup b x of
  Just c  -> c
  Nothing -> 0

-- | Finds the term with the largest generator (in the natural ordering of the generators)
findMaxTerm :: (Ord b) => FreeMod c b -> Maybe (b,c)
findMaxTerm (FreeMod m) = if Map.null m
  then Nothing
  else Just (Map.findMax m)

-- | Finds the term with the smallest generator (in the natural ordering of the generators)
findMinTerm :: (Ord b) => FreeMod c b -> Maybe (b,c)
findMinTerm (FreeMod m) = if Map.null m
  then Nothing
  else Just (Map.findMin m)

--------------------------------------------------------------------------------
-- * Basic operations

-- | Negation
neg :: Num c => FreeMod c b -> FreeMod c b 
neg (FreeMod m) = FreeMod (Map.map negate m)

-- | Additions
add :: (Ord b, Eq c, Num c) => FreeMod c b -> FreeMod c b -> FreeMod c b
add (FreeMod m1) (FreeMod m2) = FreeMod (Map.mergeWithKey f id id m1 m2) where
  f _ x y = case x+y of { 0 -> Nothing ; z -> Just z }

-- | Subtraction
sub :: (Ord b, Eq c, Num c) => FreeMod c b -> FreeMod c b -> FreeMod c b
sub (FreeMod m1) (FreeMod m2) = FreeMod (Map.mergeWithKey f id (Map.map negate) m1 m2) where
  f _ x y = case x-y of { 0 -> Nothing ; z -> Just z }

-- | Scaling by a number
scale :: (Ord b, Eq c, Num c) => c -> FreeMod c b -> FreeMod c b
scale 0 _           = zero
scale x (FreeMod m) = FreeMod (Map.mapMaybe f m) where
  f y = case x*y of { 0 -> Nothing ; z -> Just z }

-- | Dividing by a number (assuming that the coefficient ring is integral, and each coefficient
-- is divisible by the given number)
divideByConst :: (Ord b, Eq c, Integral c, Show c) => c -> FreeMod c b -> FreeMod c b
divideByConst d (FreeMod m) = FreeMod (Map.mapMaybe f m) where
  f a = case divMod a d of
    (b,0) -> case b of { 0 -> Nothing ; z -> Just z }
    _     -> error $ "FreeMod/divideByConst: not divisible by " ++ show d

-- | Addition after scaling: @A + c*B@. 
addScale :: (Ord b, Eq c, Num c) => FreeMod c b -> c -> FreeMod c b -> FreeMod c b
addScale (FreeMod m1) cf (FreeMod m2) = 
  if cf == 0 
    then FreeMod m1 
    else FreeMod (Map.mergeWithKey f id (Map.mapMaybe g) m1 m2) 
  where
    g     y = case     cf*y of { 0 -> Nothing ; z -> Just z }
    f _ x y = case x + cf*y of { 0 -> Nothing ; z -> Just z }

-- | Subtraction after scaling: @A - c*B@. This is a handy optimization for conversion algorithms.
subScale :: (Ord b, Eq c, Num c) => FreeMod c b -> c -> FreeMod c b -> FreeMod c b
subScale (FreeMod m1) cf (FreeMod m2) = 
  if cf == 0 
    then FreeMod m1 
    else FreeMod (Map.mergeWithKey f id (Map.mapMaybe g) m1 m2) 
  where
    g     y = case   - cf*y of { 0 -> Nothing ; z -> Just z }
    f _ x y = case x - cf*y of { 0 -> Nothing ; z -> Just z }

--------------------------------------------------------------------------------

-- | Summation
sum :: (Ord b, Eq c, Num c) => [FreeMod c b] -> FreeMod c b
sum []  = zero
sum zms = (foldl1' add) zms

-- | Linear combination
linComb :: (Ord b, Eq c, Num c) => [(c, FreeMod c b)] -> FreeMod c b
linComb = sumWith where

   sumWith :: (Ord b, Eq c, Num c) => [(c, FreeMod c b)] -> FreeMod c b
   sumWith []  = zero
   sumWith zms = sum [ scale c zm | (c,zm) <- zms ]

-- | Expand each generator into a term in another module and then sum the results
flatMap :: (Ord b1, Ord b2, Eq c, Num c) => (b1 -> FreeMod c b2) -> FreeMod c b1 -> FreeMod c b2
flatMap f = sum . map g . Map.assocs . unFreeMod where
  g (x,c) = scale c (f x)

flatMap' :: (Ord b1, Ord b2, Eq c2, Num c2) => (c1 -> c2) -> (b1 -> FreeMod c2 b2) -> FreeMod c1 b1 -> FreeMod c2 b2
flatMap' embed f = sum . map g . Map.assocs . unFreeMod where
  g (x,c) = scale (embed c) (f x)

-- | The histogram of a multiset of generators is naturally an element of the given Z-module.
{-# SPECIALIZE histogram :: Ord b => [b] -> ZMod b #-} 
histogram :: (Ord b, Num c) => [b] -> FreeMod c b
histogram xs = FreeMod $ foldl' f Map.empty xs where
  f old x = Map.insertWith (+) x 1 old
  
--------------------------------------------------------------------------------
-- * Rings (at least some simple ones, where the basis form a partial monoid)

-- | The multiplicative unit
one :: (Monoid b, Num c) => FreeMod c b
one = FreeMod (Map.singleton mempty 1)

-- | A constant
konst :: (Monoid b, Eq c, Num c) => c -> FreeMod c b
konst c = FreeMod $ if c/=0 
  then Map.singleton mempty c
  else Map.empty

-- | Multiplying two ring elements
mul :: (Ord b, Monoid b, Eq c, Num c) => FreeMod c b -> FreeMod c b -> FreeMod c b
mul = mulWith (<>)

-- | Multiplying two ring elements, when the base forms a partial monoid
mul' :: (Ord b, PartialMonoid b, Eq c, Num c) => FreeMod c b -> FreeMod c b -> FreeMod c b
mul' = mulWith' (pmAdd)

-- | Product
product :: (Ord b, Monoid b, Eq c, Num c) => [FreeMod c b] -> FreeMod c b
product []  = generator mempty
product xs  = foldl1' mul xs

-- | Product, when the base forms a partial monoid
product' :: (Ord b, PartialMonoid b, Eq c, Num c) => [FreeMod c b] -> FreeMod c b
product' []  = generator pmUnit
product' xs  = foldl1' mul' xs

-- | Multiplying two ring elements, using the given monoid operation on base
mulWith :: (Ord b, Eq c, Num c) => (b -> b -> b) -> FreeMod c b -> FreeMod c b -> FreeMod c b
mulWith op xx yy = normalize $ sum [ (f x c) | (x,c) <- toList xx ] where
  -- fromListWith can result in zero coefficients... 
  -- and if the sum is one term only, then it won't rmeove them :(
  f !x !c = FreeMod $ Map.fromListWith (+) [ (op x y, cd) | (y,d) <- ylist , let cd = c*d , cd /= 0 ]
  ylist = toList yy

-- | Multiplication using a \"truncated\" operation on the base
mulWith' :: (Ord b, Eq c, Num c) => (b -> b -> Maybe b) -> FreeMod c b -> FreeMod c b -> FreeMod c b
mulWith' op xx yy = normalize $ sum [ (f x c) | (x,c) <- toList xx ] where
  f !x !c = FreeMod $ Map.fromListWith (+) [ (z, cd) | (y,d) <- ylist , Just z <- [op x y] , let cd = c*d , cd /= 0 ]
  ylist = toList yy

mulWith'' :: (Ord b, Eq c, Num c) => (b -> b -> Maybe (b,c)) -> FreeMod c b -> FreeMod c b -> FreeMod c b
mulWith'' op xx yy = normalize $ sum [ (f x c) | (x,c) <- toList xx ] where
  f !x !c = FreeMod $ Map.fromListWith (+) [ (z, cde) | (y,d) <- ylist , Just (z,e) <- [op x y] , let cde = c*d*e , cde /= 0 ]
  ylist = toList yy

-- | Product, using the given Monoid empty and operation. 
--
-- Implementation note: we only use the user-supported 
-- empty value in case of an empty product.
productWith :: (Ord b, Eq c, Num c) => b -> (b -> b -> b) -> [FreeMod c b] -> FreeMod c b
productWith empty op []  = generator empty
productWith empty op xs  = foldl1' (mulWith op) xs

productWith' :: (Ord b, Eq c, Num c) => b -> (b -> b -> Maybe b) -> [FreeMod c b] -> FreeMod c b
productWith' empty op []  = generator empty
productWith' empty op xs  = foldl1' (mulWith' op) xs

productWith'' :: (Ord b, Eq c, Num c) => b -> (b -> b -> Maybe (b,c)) -> [FreeMod c b] -> FreeMod c b
productWith'' empty op []  = generator empty
productWith'' empty op xs  = foldl1' (mulWith'' op) xs

-- | Multiplies by a monomial
mulByMonom :: (Eq c, Num c, Ord b, Monoid b) => b -> FreeMod c b -> FreeMod c b
mulByMonom monom = mapBase (mappend monom) 

-- | Multiplies by a monomial (NOTE: we assume that this is an injective operation!!!)
unsafeMulByMonom :: (Ord b, Monoid b) => b -> FreeMod c b -> FreeMod c b
unsafeMulByMonom monom = unsafeMapBase (mappend monom)

-- | Multiplies by a partial monomial 
mulByMonom' :: (Eq c, Num c, Ord b, PartialMonoid b) => b -> FreeMod c b -> FreeMod c b
mulByMonom' monom = mapMaybeBase (pmAdd monom) 

unsafeMulByMonom' :: (Ord b, PartialMonoid b) => b -> FreeMod c b -> FreeMod c b
unsafeMulByMonom' monom = unsafeMapMaybeBase (pmAdd monom) 

--------------------------------------------------------------------------------
-- * Integer \/ Rational conversions

freeModCoeffProxy :: FreeMod c b -> Proxy c
freeModCoeffProxy _ = Proxy

{-
typeRepZ, typeRepQ :: TypeRep
typeRepZ = typeOf (0 :: Integer ) 
typeRepQ = typeOf (0 :: Rational)
-}

-- | This is an optimized coefficient ring change function. It detects runtime whether the output 
-- coefficient ring is also the integers, and does nothing in that case. 
fromZMod :: (Num c, Typeable c, Eq c, Num c, Ord b, Typeable b) => ZMod b -> FreeMod c b
fromZMod = unsafeCoeffChange fromInteger

-- | This is an optimized coefficient ring change function. It detects runtime whether the output 
-- coefficient ring is also the rational, and does nothing in that case. 
fromQMod :: (Fractional c, Typeable c, Eq c, Num c, Ord b, Typeable b) => QMod b -> FreeMod c b
fromQMod = unsafeCoeffChange fromRational

-- | This is an optimized coefficient ring change function. It detects runtime whether the output 
-- coefficient ring is the same as the input, and does nothing in that case. 
--
-- For this to be valid, it is required that the supported function is identity in
-- the case @c1 ~ c2@ !!!
unsafeCoeffChange :: (Typeable c1, Typeable c2, Eq c2, Num c2, Ord b, Typeable b) => (c1 -> c2) -> FreeMod c1 b -> FreeMod c2 b
unsafeCoeffChange f input = case cast input of
  Just out -> {- trace "*** no cast" $ -} out
  Nothing  -> {- trace "!!! cast"    $ -} mapCoeff f input

-- | Given a polynomial with formally rational coefficients, but whose coeffiecients
-- are actually integers, we return the corresponding polynomial with integer coefficients
unsafeZModFromQMod :: Ord b => QMod b -> ZMod b
unsafeZModFromQMod = mapCoeff f where
  f :: Rational -> Integer
  f q = if denominator q == 1 then numerator q else error "unsafeZModFromQMod: coefficient is not integral"

--------------------------------------------------------------------------------
-- * Misc

-- | Changing the base set
mapBase :: (Ord a, Ord b, Eq c, Num c) => (a -> b) -> FreeMod c a -> FreeMod c b
mapBase f 
  = normalize                            -- it can happen that we merge a (-1) and (+1) for example ...
  . onFreeMod (Map.mapKeysWith (+) f)

-- | Changing the base set (the user must guarantee that the map is injective!!)
unsafeMapBase :: (Ord a, Ord b) => (a -> b) -> FreeMod c a -> FreeMod c b
unsafeMapBase f = onFreeMod (Map.mapKeys f)

-- | Changing the coefficient ring
mapCoeff :: (Ord b, Eq c2, Num c2) => (c1 -> c2) -> FreeMod c1 b -> FreeMod c2 b
mapCoeff f = onFreeMod' (Map.mapMaybe mbf) where
  mbf x = case f x of { 0 -> Nothing ; y -> Just y }

mapCoeffWithKey :: (Ord b, Eq c2, Num c2) => (b -> c1 -> c2) -> FreeMod c1 b -> FreeMod c2 b
mapCoeffWithKey f = onFreeMod' (Map.mapMaybeWithKey mbf) where
  mbf k x = case f k x of { 0 -> Nothing ; y -> Just y }

-- | Extract a subset of terms
filterBase :: (Ord b) => (b -> Bool) -> FreeMod c b -> FreeMod c b
filterBase f = onFreeMod (Map.filterWithKey g) where g k _ = f k 

-- | Map and extract a subset of terms 
mapMaybeBase :: (Ord a, Ord b, Eq c, Num c) => (a -> Maybe b) -> FreeMod c a -> FreeMod c b
mapMaybeBase f 
  = normalize      -- it can happen that we merge a (-1) and (+1) for example ...
  . onFreeMod (Map.fromListWith (+) . mapMaybe g . Map.toList)
  where
    g (k,x) = case f k of { Just k' -> Just (k',x) ; Nothing -> Nothing }

-- | Like 'mapMaybeBase', but the user must guarantee that the @Just@ part of the map is injective!
unsafeMapMaybeBase :: (Ord a, Ord b) => (a -> Maybe b) -> FreeMod c a -> FreeMod c b
unsafeMapMaybeBase f = onFreeMod (Map.fromList . mapMaybe g . Map.toList)
  where
    g (k,x) = case f k of { Just k' -> Just (k',x) ; Nothing -> Nothing }

mapMaybeBaseCoeff :: (Ord a, Ord b, Eq c, Num c) => (a -> Maybe (b,c)) -> FreeMod c a -> FreeMod c b
mapMaybeBaseCoeff f 
  = normalize      -- it can happen that we merge a (-1) and (+1) for example ...
  . onFreeMod (Map.fromListWith (+) . mapMaybe g . Map.toList)
  where
    g (k,x) = case f k of { Just (k',y) -> Just (k',x*y) ; Nothing -> Nothing }

-- | NOTE: This is UNSAFE! The user must guarantee that the map respects the invariants!
onFreeMod :: (Ord a, Ord b) => (Map a c -> Map b c) -> FreeMod c a -> FreeMod c b
onFreeMod f = FreeMod . f . unFreeMod

onFreeMod' :: (Ord a, Ord b) => (Map a c -> Map b d) -> FreeMod c a -> FreeMod d b
onFreeMod' f = FreeMod . f . unFreeMod

--------------------------------------------------------------------------------
