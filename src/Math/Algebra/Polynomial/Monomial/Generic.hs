
-- | Multivariate monomials where the set of variables is given by 
-- the inhabitants of a type

{-# LANGUAGE CPP, BangPatterns, TypeFamilies, KindSignatures, StandaloneDeriving, FlexibleContexts #-}
module Math.Algebra.Polynomial.Monomial.Generic where

--------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import Data.Foldable as F

import Data.Proxy
import Data.Typeable

#if MIN_VERSION_base(4,11,0)        
import Data.Semigroup
import Data.Monoid
import Data.List.NonEmpty ( NonEmpty )
#else
import Data.Monoid
#endif

import qualified Data.Map.Strict as Map ; import Data.Map.Strict (Map)

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.FreeModule
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------
-- * Monomials

-- | A monomial over the set of variables represented by the inhabitants 
-- of the type @v@.
-- The invariant we keep is that the exponents present in the @Map@ are always positive.
newtype Monom v 
  = Monom (Map v Int)
  deriving (Eq,Ord,Show,Typeable)

unMonom :: Monom v -> Map v Int
unMonom (Monom table) = table

normalizeMonom :: Ord v => Monom v -> Monom v 
normalizeMonom (Monom m) = Monom $ Map.filter (>0) m

isNormalMonom :: Monom v -> Bool
isNormalMonom (Monom m) = all (>0) (Map.elems m)

monomToList :: Ord v => Monom v -> [(v,Int)]
monomToList (Monom m) = Map.toList m

monomFromList :: Ord v => [(v,Int)] -> Monom v
monomFromList list = Monom $ Map.fromList $ filter f list where
  f (v,e) | e <  0    = error "monomFromList: negative exponent"
          | e == 0    = False
          | otherwise = True

-- | Note: we can collapse variables together!
mapMonom :: (Ord v, Ord w) => (v -> w) -> Monom v -> Monom w
mapMonom f (Monom old) = Monom $ Map.mapKeysWith (+) f old 

emptyMonom :: Monom v
emptyMonom = Monom Map.empty

isEmptyMonom :: Monom v -> Bool
isEmptyMonom (Monom m) = Map.null m

mulMonom :: Ord v => Monom v -> Monom v -> Monom v
mulMonom (Monom m1) (Monom m2) = Monom (Map.unionWith (+) m1 m2)

{-# SPECIALIZE prodMonoms :: Ord v => [Monom v] ->  Monom v #-}
prodMonoms :: (Foldable f, Ord v) => f (Monom v) -> Monom v
prodMonoms list = Monom $ Map.unionsWith (+) $ map unMonom $ F.toList list

powMonom :: Ord v => Monom v -> Int -> Monom v
powMonom (Monom m) e 
  | e < 0     = error "powMonom: expecting a non-negative exponent"
  | e == 0    = emptyMonom
  | otherwise = Monom (Map.map (*e) m)

varMonom :: Ord v => v -> Monom v
varMonom v = Monom (Map.singleton v 1)

singletonMonom :: Ord v => v -> Int -> Monom v
singletonMonom v e 
  | e < 0     = error "singletonMonom: expecting a non-negative exponent"
  | e == 0    = emptyMonom
  | otherwise = Monom (Map.singleton v e)

maxDegMonom :: Monom v -> Int
maxDegMonom (Monom m) = maximum (Map.elems m)

totalDegMonom :: Monom v -> Int
totalDegMonom (Monom m) = sum' (Map.elems m)

evalMonom :: (Num c, Ord v) => (v -> c) -> Monom v -> c
evalMonom f (Monom m) = foldl' (*) 1 (map g $ Map.toList m) where
  g (v,e) = f v ^ e

termSubsMonom :: (Num c, Ord v) => (v -> Maybe c) -> (Monom v, c) -> (Monom v, c)
termSubsMonom f (Monom m , c0) = (Monom m' , c0*proj) where
  m'   = Map.fromList $ catMaybes mbs
  list = Map.toList m
  (proj, mbs)  = mapAccumL g 1 list 
  g !s (!v,!e) = case f v of
    Nothing     -> ( s       , Just (v,e) )   
    Just c      -> ( s * c^e , Nothing    )

--------------------------------------------------------------------------------

-- Semigroup became a superclass of Monoid
#if MIN_VERSION_base(4,11,0)        

{-# SPECIALIZE prodMonoms :: Ord v => NonEmpty (Monom v) ->  Monom v #-}

instance Ord v => Semigroup (Monom v) where
  (<>)    = mulMonom
  sconcat = prodMonoms

instance Ord v => Monoid (Monom v)  where
  mempty  = emptyMonom
  mconcat = prodMonoms

#else

instance Ord v => Monoid (Monom v) where
  mempty  = emptyMonom
  mappend = mulMonom
  mconcat = prodMonoms

#endif

--------------------------------------------------------------------------------

instance Pretty v => Pretty (Monom v) where
  pretty (Monom m) = worker (Map.toList m) where
    worker []    = "1"
    worker pairs = intercalate "*" (map f pairs) where
      f (b,0) = "1"                                      -- shouldn't normall happen
      f (b,1) = pretty b
      f (b,k) = pretty b ++ "^" ++ show k

--------------------------------------------------------------------------------

instance (Ord v, Pretty v) => Monomial (Monom v) where
  type VarM (Monom v) = v
  normalizeM  = normalizeMonom
  isNormalM   = isNormalMonom
  fromListM   = monomFromList
  toListM     = monomToList
  emptyM      = emptyMonom
  isEmptyM    = isEmptyMonom
  variableM   = varMonom
  singletonM  = singletonMonom
  mulM        = mulMonom
  productM    = prodMonoms
  powM        = powMonom
  maxDegM     = maxDegMonom              
  totalDegM   = totalDegMonom
  evalM       = evalMonom
  varSubsM    = mapMonom
  termSubsM   = termSubsMonom

--------------------------------------------------------------------------------
