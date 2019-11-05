
-- | Legendre polynomials
--
-- See <https://en.wikipedia.org/wiki/Legendre_polynomials>
-- 

{-# LANGUAGE DataKinds, TypeSynonymInstances, FlexibleContexts, FlexibleInstances, BangPatterns, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Univariate.Legendre
  ( legendreP
  , rationalLegendreP
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

-- | Legendre polynomials
legendreP :: (Field c, KnownSymbol v) => Int -> Univariate c v
legendreP = fromQUni . renameUniVar . rationalLegendreP

--------------------------------------------------------------------------------

x :: Univariate Rational "x"
x = variableP ()

rationalLegendreP :: Int -> Univariate Rational "x"
rationalLegendreP = intCache compute where
  fi = (fromIntegral :: Int -> Rational)
  compute recur n = case n of 
    0 -> 1
    1 -> x
    n -> scaleP (1 / fi n) 
       $ scaleP (fi $ 2*n-1) (x * recur (n-1)) 
       - scaleP (fi $   n-1) (    recur (n-2))

--------------------------------------------------------------------------------

