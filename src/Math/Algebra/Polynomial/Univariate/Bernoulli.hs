
-- | Bernoulli and Euler polynomials
--
-- See <https://en.wikipedia.org/wiki/Bernoulli_polynomials>
-- 

{-# LANGUAGE DataKinds, TypeSynonymInstances, FlexibleContexts, FlexibleInstances, BangPatterns, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Univariate.Bernoulli
  ( bernoulliB, eulerE
  , rationalBernoulliB, rationalEulerE
  , bernoulliNumber, signedEulerNumber, unsignedEulerNumber
  , eulerianPolynomial
  ) 
  where

--------------------------------------------------------------------------------

import Data.List
import Data.Ratio

import Data.Semigroup
import Data.Monoid

import GHC.TypeLits

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , FreeModule(..) , ZMod , QMod )

import Math.Algebra.Polynomial.Univariate

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------
-- * Bernoulli polynomials

-- | Bernoulli polynomials
bernoulliB :: (Field c, KnownSymbol v) => Int -> Univariate c v
bernoulliB = fromQUni . renameUniVar . rationalBernoulliB

-- | Euler polynomials (not to be confused with the related Eulerian polynomials!)
eulerE :: (Field c, KnownSymbol v) => Int -> Univariate c v
eulerE = fromQUni . renameUniVar . rationalEulerE

--------------------------------------------------------------------------------

rationalBernoulliB :: Int -> Univariate Rational "x"
rationalBernoulliB n = Uni $ ZMod.fromList
  [ (U k , fromInteger (binomial n k) * bernoulliNumber (n-k) ) | k<-[0..n] ]

rationalEulerE :: Int -> Univariate Rational "x"
rationalEulerE n = sumP
  [ scaleP coeff $ xMinusHalfPowN (n-k)
  | k <- [0,2..n]
  , let coeff = fromInteger (binomial n k * eulerNumber k) / 2^k 
  ]
  where
    eulerNumber k = if even k 
      then signedEulerNumber (div k 2) 
      else 0

xMinusHalfPowN :: Int -> Univariate Rational "x"
xMinusHalfPowN = intCache compute where
  x_minus_half = Uni $ ZMod.fromList [ (U 1 , 1) , (U 0 , -1/2) ]
  compute recur n = case n of 
    0 -> 1
    n -> x_minus_half * recur (n-1)

--------------------------------------------------------------------------------
-- * Bernoulli numbers

-- | Bernoulli numbers. @bernoulli 1 == -1%2@ and @bernoulli k == 0@ for
-- k>2 and /odd/. This function uses the formula involving Stirling numbers
-- of the second kind. Numerators: A027641, denominators: A027642.
bernoulliNumber :: Integral a => a -> Rational
bernoulliNumber n 
  | n <  0    = error "bernoulli: n should be nonnegative"
  | n == 0    = 1
  | n == 1    = -1/2
  | otherwise = sum [ f k | k<-[1..n] ] 
  where
    f k = toRational (negateIfOdd (n+k) $ factorial k * stirling2nd n k) 
        / toRational (k+1)

--------------------------------------------------------------------------------
-- * Euler numbers

{-
x, oneminusx, xoneminusx, halfoneminusx :: Univariate Rational "x"
x = variableP ()
oneminusx = 1 - x
xoneminusx = x * (1 - x)
halfoneminusx = scaleP (1/2) oneminusx
nx :: Int -> Univariate Rational "x"
nx n = monomP' (U 1) (fromIntegral n)

scaledEulerianPolynomial :: Int -> Univariate Rational "x"
scaledEulerianPolynomial = intCache compute where
  compute recur n = case n of 
    0 -> 1
    n -> (nx n + halfoneminusx) * recur (n-1) + xoneminusx * differentiateUni (recur (n-1))
-}

x, oneminusx, two_xoneminusx :: Univariate Integer "x"
x = variableP ()
oneminusx = 1 - x
two_xoneminusx = 2 * x * (1 - x)
two_nx :: Int -> Univariate Integer "x"
two_nx n = monomP' (U 1) (2 * fromIntegral n)

-- | Eulerian polynomials (row polynomials of A060187)
eulerianPolynomial :: Int -> Univariate Integer "x"
eulerianPolynomial = intCache compute where
  compute recur n = case n of 
    0 -> 1
    n -> (two_nx n + oneminusx) * recur (n-1) + two_xoneminusx * differentiateUni (recur (n-1))

-- | Signed Euler numbers (unsigned version: A000364)
--
-- See <https://en.wikipedia.org/wiki/Euler_number>
--
-- NOTE: we skip the zeros (every other index)
signedEulerNumber :: Int -> Integer
signedEulerNumber = intCache compute where
  compute _ n = div (evalP id (\_ -> -1) $ eulerianPolynomial (2*n)) (4^n)

-- | unsigned Euler numbers (A000364)
--
-- NOTE: we skip the zeros (every other index)
unsignedEulerNumber :: Int -> Integer
unsignedEulerNumber n = negateIfOdd n $ signedEulerNumber n

--------------------------------------------------------------------------------

