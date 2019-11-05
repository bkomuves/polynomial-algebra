
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

import Data.Map.Strict (Map) ; import qualified Data.Map.Strict as Map 

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

divMonom :: Ord v => Monom v -> Monom v -> Maybe (Monom v)
divMonom (Monom m1) (Monom m2) = 
  if all (>=0) (Map.elems pre_monom) 
    then Just $ Monom pre_monom
    else Nothing
  where
    minus_m2  = Map.map negate m2
    pre_monom = Map.filter (/=0) 
              $ Map.unionWith (+) m1 minus_m2

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
-- * differentiation

diffMonom :: (Ord v, Num c) => v -> Int -> Monom v -> Maybe (Monom v, c)
diffMonom _ 0 mon           = Just (mon,1)
diffMonom v k (Monom table) =
  if k > m 
    then Nothing
    else Just (Monom table' , fromInteger c) 
  where
    m      = Map.findWithDefault 0 v table
    table' = Map.insert v (m-k) table
    c      = Data.List.product [ fromIntegral (m-i) | i<-[0..k-1] ] :: Integer

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
  divM        = divMonom
  productM    = prodMonoms
  powM        = powMonom
  maxDegM     = maxDegMonom              
  totalDegM   = totalDegMonom
  diffM       = diffMonom
  evalM       = evalMonom
  varSubsM    = mapMonom
  termSubsM   = termSubsMonom

--------------------------------------------------------------------------------
