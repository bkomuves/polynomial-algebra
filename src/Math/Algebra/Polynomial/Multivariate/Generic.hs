
-- | Multivariate polynomial algebra where the set of variables is given by 
-- the inhabitants of a type

{-# LANGUAGE BangPatterns, TypeFamilies, KindSignatures, StandaloneDeriving, FlexibleContexts #-}
module Math.Algebra.Polynomial.Multivariate.Generic where

--------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import Data.Foldable as F

import Data.Proxy
import Data.Typeable

import qualified Data.Map.Strict as Map ; import Data.Map.Strict (Map)

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , FreeModule(..) ) -- , ZMod , QMod )

import Math.Algebra.Polynomial.Monomial.Generic 

import Math.Algebra.Polynomial.Class
-- import Math.Algebra.Polynomial.FreeModule
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------

newtype Poly (coeff :: *) (var :: *)
  = Poly (FreeMod coeff (Monom var) )
  deriving (Eq,Ord,Show,Typeable)

unPoly :: Poly c v -> FreeMod c (Monom v) 
unPoly (Poly p) = p

instance FreeModule (Poly c v) where
  type BaseF  (Poly c v) = Monom v
  type CoeffF (Poly c v) = c
  toFreeModule   = unPoly
  fromFreeModule = Poly

--------------------------------------------------------------------------------

instance (Ring c, Ord v, Pretty v) => AlmostPolynomial (Poly c v) where
  type CoeffP (Poly c v) = c
  type MonomP (Poly c v) = Monom v
  type VarP   (Poly c v) = v

  fromListP     = Poly . ZMod.fromList
  toListP       = ZMod.toList . unPoly

  zeroP         = Poly ZMod.zero
  isZeroP       = ZMod.isZero . unPoly
  oneP          = Poly (ZMod.generator emptyMonom)

  variableP     = Poly . ZMod.generator . varMonom
  singletonP    = \v e -> Poly (ZMod.generator (singletonMonom v e))
  monomP        = \m     -> Poly $ ZMod.generator m
  scalarP       = \s     -> Poly $ ZMod.singleton emptyMonom s

  addP          = \p1 p2 -> Poly $ ZMod.add (unPoly p1) (unPoly p2)
  subP          = \p1 p2 -> Poly $ ZMod.sub (unPoly p1) (unPoly p2)
  negP          = Poly . ZMod.neg . unPoly
  mulP          = \p1 p2 -> Poly $ ZMod.mulWith     mulMonom (unPoly p1) (unPoly p2)
  productP      = \ps    -> Poly $ ZMod.productWith emptyMonom mulMonom $ map unPoly ps

  coeffOfP      = \m p   -> ZMod.coeffOf m (unPoly p)
  mulByMonomP   = \m p   -> Poly $ ZMod.unsafeMulByMonom m (unPoly p)
  scaleP        = \s p   -> Poly $ ZMod.scale s (unPoly p) 

instance (Ring c, Ord v, Pretty v) => Polynomial (Poly c v) where
  evalP         = \g f p -> let { !z = evalM f ; h (!m,!c) = g c * z m } in sum' $ map h $ ZMod.toList $ unPoly p
  varSubsP      = \f p   -> Poly $ ZMod.mapBase (mapMonom f) (unPoly p)
  coeffSubsP    = \f p   -> Poly $ ZMod.fromList $ map (termSubsMonom f) $ ZMod.toList $ unPoly p 
  subsP         = \f p   -> Poly $ ZMod.flatMap (evalMonom (unPoly . f)) (unPoly p)

instance (Ring c, Ord v, Pretty v) => Num (Poly c v) where
  fromInteger = scalarP . fromInteger
  (+)    = addP
  (-)    = subP
  negate = negP
  (*)    = mulP
  abs    = id
  signum = \_ -> scalarP 1

instance (Ring c, Ord v, Pretty v, Pretty (Monom v)) => Pretty (Poly c v) where
  pretty poly@(Poly fm) = if isSignedR (proxyCoeffP poly)
    then prettyFreeMod'  True   pretty fm
    else prettyFreeMod'' pretty pretty fm

-- hackety hack hack...
instance IsSigned (Poly c v) where
  signOf = const (Just Plus)

-- So that we can use it again as a coefficient ring
instance (Ring c, Ord v, Show v, Pretty v) => Ring (Poly c v) where
  isZeroR   = ZMod.isZero . unPoly
  isAtomicR = const False
  isSignedR = const False
  absR      = id
  signumR   = const (Just Plus)

--------------------------------------------------------------------------------
