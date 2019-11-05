
-- | Hermit polynomials
--
-- See <https://en.wikipedia.org/wiki/Hermite_polynomials>
-- 

{-# LANGUAGE DataKinds, TypeSynonymInstances, FlexibleContexts, FlexibleInstances, BangPatterns, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Univariate.Hermite
  ( hermiteH
  , hermiteHe
  , integralHermiteH
  , integralHermiteHe
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

-- | Probabilists\' Hermite polynomials
hermiteHe :: (Ring c, KnownSymbol v) => Int -> Univariate c v
hermiteHe = fromZUni . renameUniVar . integralHermiteHe

-- | Physicists\' Hermite polynomials
hermiteH :: (Ring c, KnownSymbol v) => Int -> Univariate c v
hermiteH = fromZUni . renameUniVar . integralHermiteH

--------------------------------------------------------------------------------

x, twox :: Univariate Integer "x"
x    = variableP ()
twox = monomP'   (U 1) 2

-- | Probabilists\' Hermite polynomials
integralHermiteHe :: Int -> Univariate Integer "x"
integralHermiteHe = intCache compute where
  compute recur n = case n of 
    0 -> 1
    1 -> x
    n -> x * recur (n-1) - differentiateUni (recur (n-1))

-- | Physicists\' Hermite polynomials
integralHermiteH :: Int -> Univariate Integer "x"
integralHermiteH = intCache compute where
  compute recur n = case n of 
    0 -> 1
    1 -> twox
    n -> twox * recur (n-1) - differentiateUni (recur (n-1))

--------------------------------------------------------------------------------

