
-- | Univariate \"monomials\" (basically the natural numbers)

{-# LANGUAGE BangPatterns, DataKinds, KindSignatures, TypeFamilies #-}
module Math.Algebra.Polynomial.Monomial.Univariate where

--------------------------------------------------------------------------------

import Data.Array ( assocs ) 
import Data.List

#if MIN_VERSION_base(4,11,0)        
import Data.Semigroup
import Data.Monoid
#else
import Data.Monoid
#endif

import Data.Typeable
import GHC.TypeLits
import Data.Proxy

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------
-- * Univariate monomials

-- | A monomial in a univariate polynomial, indexed by its name, eg @U "x"@
newtype U (var :: Symbol) = U Int deriving (Eq,Ord,Show,Typeable)

-- | Name of the variable
uVar :: KnownSymbol var => U var -> String
uVar = symbolVal . uproxy where
  uproxy :: U var -> Proxy var
  uproxy _ = Proxy

instance KnownSymbol var => Pretty (U var) where
  pretty u@(U e) = case e of
    0 -> "1"
    1 -> uVar u
    _ -> uVar u ++ "^" ++ show e

--------------------------------------------------------------------------------

#if MIN_VERSION_base(4,11,0)        

instance Semigroup (U var) where
  (<>) (U e) (U f) = U (e+f)

instance Monoid (U var) where
  mempty = U 0
  mappend (U e) (U f) = U (e+f)
  mconcat us = U $ sum' [ e | U e <- us ]

#else

instance Monoid (U var) where
  mempty  = U 0
  mappend (U e) (U f) = U (e+f)
  mconcat us = U $ sum' [ e | U e <- us ]

#endif

--------------------------------------------------------------------------------

instance KnownSymbol var => Monomial (U var) where
  -- | the type of variables
  type VarM (U var) = ()
  
  -- checking the invariant
  normalizeM  = id
  isNormalM   = const True

  -- construction and deconstruction
  fromListM   ves = U $ sum' (map snd ves)
  toListM     (U e) = [((),e)]

  -- simple monomials
  emptyM      = U 0
  isEmptyM    (U e) = (e==0)
  variableM   _   = U 1
  singletonM  _ e = U e

  -- algebra
  mulM         = mappend
  productM     = mconcat
  divM (U e) (U f) = if e >= f then Just (U (e-f)) else Nothing
  powM (U e) k = U (k*e)

  -- degrees
  maxDegM     (U e) = e
  totalDegM   (U e) = e

  -- calculus
  diffM _ = diffU

  -- substitution and evaluation
  evalM       f (U e) = (f ())^e
  varSubsM    _ = id
  termSubsM   f (U e, c) = case f () of  
                Nothing  -> (U e, c      )
                (Just x) -> (U 0, c * x^e)

--------------------------------------------------------------------------------
-- * differentiation

diffU :: Num c => Int -> U v -> Maybe (U v, c)
diffU k (U m) =
  if k > m 
    then Nothing
    else Just (U (m-k) , fromInteger c) 
  where
    c = product [ fromIntegral (m-i) | i<-[0..k-1] ] :: Integer

--------------------------------------------------------------------------------
