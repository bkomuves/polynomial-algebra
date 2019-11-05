
-- | Multivariate polynomials where the variable set is the countably infinite
-- set @{x_1, x_2, x_3, ...}@ 

{-# LANGUAGE 
      BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables,
      FlexibleContexts
  #-}
module Math.Algebra.Polynomial.Multivariate.Infinite
  (
    Poly(..) , unPoly , polyVar , renamePolyVar
  , ZPoly , QPoly , fromZPoly, fromQPoly
  , truncate
  , XInf(..)
  )
  where

--------------------------------------------------------------------------------

import Prelude hiding ( truncate )

import Data.Maybe
import Data.List
import Data.Array.Unboxed 

import Data.Typeable
import GHC.TypeLits
import Data.Proxy
import Unsafe.Coerce as Unsafe

import Data.Foldable as F 

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , FreeModule(..) ) -- , ZMod , QMod )

import Math.Algebra.Polynomial.Monomial.Infinite

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

import qualified Math.Algebra.Polynomial.Monomial.Indexed     as Fin
import qualified Math.Algebra.Polynomial.Multivariate.Indexed as Fin

--------------------------------------------------------------------------------
-- * Polynomials

-- | A multivariate polynomial in with a given coefficient ring. 
--
-- It is also indexed by the (shared) /name/ of the variables and the /number of/
-- variable. For example @Polyn Rational "x" 3@ the type of polynomials in the
-- variables @x1, x2, x3@ with rational coefficients.
newtype Poly (coeff :: *) (var :: Symbol) 
  = Poly (FreeMod coeff (XInf var))
  deriving (Eq,Ord,Show,Typeable)

unPoly :: Poly c v -> FreeMod c (XInf v) 
unPoly (Poly p) = p

-- | Name of the variables
polyVar :: KnownSymbol var => Poly c var -> String
polyVar = symbolVal . varProxy where
  varProxy :: Poly c var -> Proxy var
  varProxy _ = Proxy

instance FreeModule (Poly c v) where
  type BaseF  (Poly c v) = XInf v 
  type CoeffF (Poly c v) = c
  toFreeModule   = unPoly
  fromFreeModule = Poly

renamePolyVar :: Poly c var1 -> Poly c var2 
renamePolyVar = Unsafe.unsafeCoerce

--------------------------------------------------------------------------------

type ZPoly = Poly Integer
type QPoly = Poly Rational

-- | Change the coefficient ring (from integers)
fromZPoly :: (Ring c, KnownSymbol v) => Poly Integer v -> Poly c v 
fromZPoly= Poly . ZMod.fromZMod . unPoly

-- | Change the coefficient field (from rationals)
fromQPoly :: (Field c, KnownSymbol v) => Poly Rational v -> Poly c v 
fromQPoly = Poly . ZMod.fromQMod . unPoly

--------------------------------------------------------------------------------

instance (Ring c, KnownSymbol v) => AlmostPolynomial (Poly c v) where
  type CoeffP (Poly c v) = c
  type MonomP (Poly c v) = XInf v
  type VarP   (Poly c v) = Index

  zeroP         = Poly ZMod.zero
  isZeroP       = ZMod.isZero . unPoly
  oneP          = Poly (ZMod.generator emptyM)

  fromListP     = Poly . ZMod.fromList
  toListP       = ZMod.toList . unPoly

  variableP     = Poly . ZMod.generator . variableXInf
  singletonP    = \v e -> Poly (ZMod.generator (singletonXInf v e))
  monomP        = \m     -> Poly $ ZMod.generator m
  monomP'       = \m c   -> Poly $ ZMod.singleton m c
  scalarP       = \s     -> Poly $ ZMod.singleton emptyXInf s

  addP          = \p1 p2 -> Poly $ ZMod.add (unPoly p1) (unPoly p2)
  subP          = \p1 p2 -> Poly $ ZMod.sub (unPoly p1) (unPoly p2)
  negP          = Poly . ZMod.neg . unPoly
  mulP          = \p1 p2 -> Poly $ ZMod.mulWith     mulXInf (unPoly p1) (unPoly p2)

  coeffOfP      = \m p   -> ZMod.coeffOf m (unPoly p)
  productP      = \ps    -> Poly $ ZMod.productWith emptyXInf mulXInf $ map unPoly ps
  mulByMonomP   = \m p   -> Poly $ ZMod.mulByMonom  m (unPoly p)
  scaleP        = \s p   -> Poly $ ZMod.scale s (unPoly p) 

instance (Ring c, KnownSymbol v) => Polynomial (Poly c v) where
  evalP         = \g f p -> let { !z = evalM f ; h (!m,!c) = g c * z m } in sum' $ map h $ ZMod.toList $ unPoly p
  varSubsP      = \f p   -> Poly $ ZMod.mapBase (varSubsM f) (unPoly p)
  coeffSubsP    = \f p   -> Poly $ ZMod.fromList $ map (termSubsM f) $ ZMod.toList $ unPoly p 
  subsP         = \f p   -> Poly $ ZMod.flatMap (evalM (unPoly . f)) (unPoly p)

instance (Ring c, KnownSymbol v) => Num (Poly c v) where
  fromInteger = scalarP . fromInteger
  (+)    = addP
  (-)    = subP
  negate = negP
  (*)    = mulP
  abs    = id
  signum = \_ -> scalarP 1

instance (Ring c, KnownSymbol v, Pretty (XInf v)) => Pretty (Poly c v) where
  pretty poly@(Poly fm) = if isSignedR (proxyCoeffP poly)
    then prettyFreeMod'  True   pretty fm
    else prettyFreeMod'' pretty pretty fm

-- hackety hack hack...
instance IsSigned (Poly c v) where
  signOf = const (Just Plus)

-- So that we can use it again as a coefficient ring
instance (Ring c, KnownSymbol v) => Ring (Poly c v) where
  isZeroR   = ZMod.isZero . unPoly
  isAtomicR = const False
  isSignedR = const False
  absR      = id
  signumR   = const (Just Plus)

--------------------------------------------------------------------------------

-- | We can always truncate to a given number of variables, simply 
-- by substituting zero to the rest
truncate :: (Eq c, Num c, KnownNat n) => Poly c v -> Fin.Poly c v n
truncate input@(Poly inpoly) = output where
  n = Fin.nOfPoly output
  output = Fin.Poly $ ZMod.mapMaybeBase f inpoly
  f (XInf es) =
      let (fs,rest) = splitAt n es
      in  if all (==0) rest 
            then Just (Fin.xsFromExponents fs) 
            else Nothing 

--------------------------------------------------------------------------------
    
