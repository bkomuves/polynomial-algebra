
-- | Cyclotomic polynomials
-- 

{-# LANGUAGE DataKinds, TypeSynonymInstances, FlexibleContexts, FlexibleInstances, BangPatterns, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Univariate.Cyclotomic 
  ( cyclotomic
  , cyclotomicMoebius
  , cyclotomicNaive
  ) 
  where

--------------------------------------------------------------------------------

import Data.Ratio

import Data.Semigroup
import Data.Monoid

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , FreeModule(..) , ZMod , QMod )

import Math.Algebra.Polynomial.Univariate

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------

-- | test whether the product of cyclotomic polynomials @Phi_d$ for the divisors @d@ of @n@ is @x^n-1@
test_product :: Int -> Bool
test_product n = lhs == rhs where
  lhs = product [ cyclotomic d | d <- divisors n ] 
  rhs = Uni $ ZMod.fromList [ (U n , 1) , (U 0 , -1) ]

-- | Synonym to 'cyclotomicMoebius'
cyclotomic :: Int -> Univariate Integer "x" 
cyclotomic = cyclotomicMoebius 

--------------------------------------------------------------------------------
-- * Implementation via Moebius inversion

-- | Cyclotomic polynomials via Moebius inversion
cyclotomicMoebius :: Int -> Univariate Integer "x"
cyclotomicMoebius = Uni . ZMod.unsafeZModFromQMod . unUni . cyclotomicMoebiusQ

cyclotomicMoebiusQ :: Int -> Univariate Rational "x" 
cyclotomicMoebiusQ n = unsafeDivide (Uni numer) (Uni denom) where
  sqfd   = squareFreeDivisors n 
  numer  = ZMod.product [ term d | (d,Plus ) <- sqfd ]
  denom  = ZMod.product [ term d | (d,Minus) <- sqfd ]
  term d = ZMod.fromList [ (U (div n d) , 1) , (U 0 , -1) ]

polynomialLongDivision :: forall p. (Polynomial p, Fractional (CoeffP p)) => p -> p -> (p,p)
polynomialLongDivision p0 q = go zeroP p0 where

  (bq,cq) = case findMaxTerm q of
    Just bc -> bc
    Nothing -> error "polynomialLongDivision: division by zero"

  go !acc !p = case findMaxTerm p of
    Nothing      -> (acc,zeroP)
    Just (bp,cp) -> case divM bp bq of
      Nothing      -> (acc,p)
      Just br      -> let cr = (cp/cq)
                          u  = scaleP cr (mulByMonomP br q)
                          p' = p - u
                          acc' = (acc + monomP' br cr) 
                      in  go acc' p' 

divideMaybe :: (Polynomial p, Fractional (CoeffP p)) => p -> p -> Maybe p
divideMaybe p q = case polynomialLongDivision p q of
  (s,r) -> if isZeroP r then Just s else Nothing

unsafeDivide :: (Polynomial p, Fractional (CoeffP p)) => p -> p -> p
unsafeDivide p q = case divideMaybe p q of
  Just s  -> s
  Nothing -> error "Polynomial/unsafeDivide: not divisible"

findMaxTerm :: FreeModule f => f -> Maybe (BaseF f, CoeffF f)
findMaxTerm = ZMod.findMaxTerm . toFreeModule

--------------------------------------------------------------------------------
-- * Naive implementation

newtype E2PiI = E2PiI Rational deriving (Eq,Ord,Show)

instance Pretty E2PiI where
  pretty (E2PiI y) = "e^{2*pi*i*" ++ show p ++ "/" ++ show q ++ "}" where
    p = numerator   y
    q = denominator y

mod1 :: Rational -> Rational
mod1 x = x - fromInteger (floor x)

mulE2PiI :: E2PiI -> E2PiI -> E2PiI
mulE2PiI (E2PiI x) (E2PiI y) = E2PiI (mod1 $ x+y)

instance Semigroup E2PiI where
  (<>) = mulE2PiI

instance Monoid E2PiI where
  mempty  = E2PiI 0
  mappend = mulE2PiI

half :: Rational
half = 1/2

reduce :: ZMod E2PiI -> Either (ZMod E2PiI) Integer
reduce input = 
  case ZMod.findMaxTerm input of
    Nothing           -> Right 0
    Just (E2PiI y, c) 
      | y == 0        -> Right   c
      | otherwise     -> case minimalZeroSumCircle y of
          Just circle     -> reduce $ ZMod.sub input (ZMod.scale c circle)
          Nothing         -> Left input

minimalZeroSumCircle :: Rational -> Maybe (ZMod E2PiI)
minimalZeroSumCircle y 
  | y < half     = Nothing
  | r == 1       = Just $ ZMod.fromList [ (E2PiI (i % q) , 1) | i<-[0..q-1] ]
  | otherwise    = Nothing
  where
    p = numerator   y
    q = denominator y
    r = q - p

--------------------------------------------------------------------------------

type X   = U "x"
type Pre = ZMod E2PiI

instance IsSigned Pre where
  signOf _ = Just Plus

preCyclotomic :: Int -> FreeMod Pre X
preCyclotomic n = ZMod.product terms where
  terms = [ ZMod.sub x (ZMod.konst (e k)) | k <- [1..n] , gcd k n == 1 ] where
  x   = ZMod.generator (U 1)
  qn  = fromIntegral n :: Rational
  e k = ZMod.generator $ E2PiI (mod1 $ fromIntegral k / qn) :: ZMod E2PiI

-- | Naive algorithm (using the direct definition of cyclotomic polynomials, and reducing
-- sums of roots of unity till they become integers)
cyclotomicNaive :: Int -> Univariate Integer "x"
cyclotomicNaive = Uni . ZMod.mapCoeff fun . preCyclotomic where
  fun term = case reduce term of
    Right c -> c
    Left {} -> error "cyclotomicNaive: shouldn't happen" 

--------------------------------------------------------------------------------
