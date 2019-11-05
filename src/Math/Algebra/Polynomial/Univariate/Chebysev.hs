
-- | Chebysev polynomials
-- 

{-# LANGUAGE DataKinds, TypeSynonymInstances, FlexibleContexts, FlexibleInstances, BangPatterns, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Univariate.Chebysev
  ( chebysevT
  , chebysevU
  , integralChebysevT 
  , integralChebysevU
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

chebysevT :: (Ring c, KnownSymbol v) => Int -> Univariate c v
chebysevT = fromZUni . renameUniVar . integralChebysevT

chebysevU :: (Ring c, KnownSymbol v) => Int -> Univariate c v
chebysevU = fromZUni . renameUniVar . integralChebysevU

--------------------------------------------------------------------------------

x, twox :: Univariate Integer "x"
x    = variableP ()
twox = monomP'   (U 1) 2

integralChebysevT :: Int -> Univariate Integer "x"
integralChebysevT = intCache compute where
  compute recur n = case n of 
    0 -> 1
    1 -> x
    n -> twox * recur (n-1) - recur (n-2)

integralChebysevU :: Int -> Univariate Integer "x"
integralChebysevU = intCache compute where
  compute recur n = case n of 
    0 -> 1
    1 -> twox
    n -> twox * recur (n-1) - recur (n-2)

--------------------------------------------------------------------------------

