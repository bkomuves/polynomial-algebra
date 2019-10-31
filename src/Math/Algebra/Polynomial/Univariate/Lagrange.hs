
-- | Lagrange interpolation

{-# LANGUAGE BangPatterns, DataKinds, KindSignatures, GeneralizedNewtypeDeriving, TypeFamilies #-}
module Math.Algebra.Polynomial.Univariate.Lagrange where

--------------------------------------------------------------------------------

import GHC.TypeLits

{-
import Data.Array ( Array , (!) , listArray , assocs ) 
import Data.List

import Data.Proxy

import Math.Algebra.Polynomial.Misc
import Math.Algebra.Polynomial.Pretty
-}

import Math.Algebra.Polynomial.Class

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , ZMod , QMod )

import Math.Algebra.Polynomial.Univariate

--------------------------------------------------------------------------------
-- * Lagrange interpolation

-- | The Lagrange interpolation for a list of @(x_i,y_i)@ pairs: the resulting polynomial P
-- is the one with minimal degree for which @P(x_i) = y_i@
lagrangeInterp :: KnownSymbol var => [(Rational,Rational)] -> Univariate Rational var 
lagrangeInterp xys = final where
  final = sumP [ scaleP (ys!!j) (lagrangePoly xs j) | j<-[0..m-1] ] where
  m = length xys
  (xs,ys) = unzip xys

-- | The minimal degree polynomial which evaluates to zero at the given inputs, except a single one
-- on which it evaluates to 1
lagrangePoly :: KnownSymbol var => [Rational] -> Int -> Univariate Rational var
lagrangePoly xs j = Uni $ ZMod.scale (1/denom) numer where
  numer  = ZMod.product [ term i    | i<-[0..m-1] , i /= j ]
  denom  = product      [ x j - x i | i<-[0..m-1] , i /= j ]
  m      = length xs
  x i    = xs !! i
  term i = ZMod.fromList 
    [ (U 1 ,     1 )
    , (U 0 , - x i )
    ]

--------------------------------------------------------------------------------
