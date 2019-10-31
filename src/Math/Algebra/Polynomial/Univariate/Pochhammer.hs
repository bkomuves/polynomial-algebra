
-- | Rising and falling factorials
--
-- See <https://en.wikipedia.org/wiki/Falling_and_rising_factorials>

{-# LANGUAGE BangPatterns, DataKinds, KindSignatures #-}
module Math.Algebra.Polynomial.Univariate.Pochhammer where

--------------------------------------------------------------------------------

import Data.Array ( Array , (!) , listArray , assocs ) 
import Data.List

import Data.Typeable
import GHC.TypeLits
import Data.Proxy

-- import Math.Combinat.Numbers

import Math.Algebra.Polynomial.Pretty

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , ZMod , QMod )

import Math.Algebra.Polynomial.Monomial.Univariate ( U(..) )
import Math.Algebra.Polynomial.Univariate

--------------------------------------------------------------------------------
-- * Polynomials using rising or falling factorials as bases

-- | Univariate polynomials using /rising factorials/ as a basis function
newtype RisingPoly  coeff = RisingPoly  { fromRisingPoly  :: FreeMod coeff RisingF }  deriving (Eq,Show)

-- | Univariate polynomials using /falling factorials/ as a basis function
newtype FallingPoly coeff = FallingPoly { fromFallingPoly :: FreeMod coeff FallingF } deriving (Eq,Show)

expandRisingPoly :: (KnownSymbol var, Typeable c, Eq c, Num c) => FreeMod c RisingF -> Univariate c var
expandRisingPoly = Uni . ZMod.flatMap (unUni . expandRisingFactorial)

expandFallingPoly :: (KnownSymbol var, Typeable c, Eq c, Num c) => FreeMod c FallingF -> Univariate c var
expandFallingPoly = Uni . ZMod.flatMap (unUni . expandFallingFactorial)

--------------------------------------------------------------------------------
-- * Rising and falling factorials 

-- | Rising factorial @x^(k) = x(x+1)(x+2)...(x+k-1)@
newtype RisingF = RF Int deriving (Eq,Ord,Show)

-- | Falling factorial @x_(k) = x(x-1)(x-2)...(x-k+1)@
newtype FallingF = FF Int deriving (Eq,Ord,Show)

instance Pretty RisingF where
  pretty (RF k) = case k of
    0 -> "1"
    1 -> "x"
    _ -> "x^(" ++ show k ++ ")"

instance Pretty FallingF where
  pretty (FF k) = case k of
    0 -> "1"
    1 -> "x"
    _ -> "x_(" ++ show k ++ ")"

expandRisingFactorial :: (KnownSymbol var, Typeable c, Eq c, Num c) => RisingF -> Univariate c var
expandRisingFactorial = Uni . ZMod.fromZMod . unUni . expandRisingFactorialZ

expandFallingFactorial ::(KnownSymbol var, Typeable c, Eq c, Num c) => FallingF -> Univariate c var
expandFallingFactorial = Uni . ZMod.fromZMod . unUni . expandFallingFactorialZ

expandRisingFactorialZ :: RisingF -> Univariate Integer var
expandRisingFactorialZ (RF k) = Uni $ ZMod.fromList
  [ (U p, abs c) | (p,c) <- assocs (signedStirling1stArray k) ]

expandFallingFactorialZ :: FallingF -> Univariate Integer var
expandFallingFactorialZ (FF k) = Uni $ ZMod.fromList
  [ (U p,     c) | (p,c) <- assocs (signedStirling1stArray k) ]

--------------------------------------------------------------------------------
-- * Stirling numbers

-- | Rows of (signed) Stirling numbers of the first kind. OEIS:A008275.
-- Coefficients of the polinomial @(x-1)*(x-2)*...*(x-n+1)@.
-- This function uses the recursion formula.
signedStirling1stArray :: Integral a => a -> Array Int Integer
signedStirling1stArray n
  | n <  1    = error "stirling1stArray: n should be at least 1"
  | n == 1    = listArray (1,1 ) [1]
  | otherwise = listArray (1,n') [ lkp (k-1) - fromIntegral (n-1) * lkp k | k<-[1..n'] ] 
  where
    prev = signedStirling1stArray (n-1)
    n' = fromIntegral n :: Int
    lkp j | j <  1    = 0
          | j >= n'   = 0
          | otherwise = prev ! j 

--------------------------------------------------------------------------------
