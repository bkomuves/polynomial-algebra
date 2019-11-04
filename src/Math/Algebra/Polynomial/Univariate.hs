
-- | Univariate polynomials

{-# LANGUAGE BangPatterns, DataKinds, KindSignatures, GeneralizedNewtypeDeriving, TypeFamilies #-}
module Math.Algebra.Polynomial.Univariate
  ( -- * Univariate polynomials
    Univariate(..) , unUni , uniVar , renameUniVar
  , ZUni , QUni
  , U(..)
  )
  where

--------------------------------------------------------------------------------

import Data.Array ( Array , (!) , listArray , assocs ) 
import Data.List

import GHC.TypeLits
import Data.Proxy
import Unsafe.Coerce as Unsafe

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Misc
import Math.Algebra.Polynomial.Pretty

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , FreeModule(..) , ZMod , QMod )

import Math.Algebra.Polynomial.Monomial.Univariate

--------------------------------------------------------------------------------
-- * Univariate polynomials

-- | A univariate polynomial with the given coefficient ring. Note: this 
-- is also indexed by the /name/ of the variable.
newtype Univariate (coeff :: *) (var :: Symbol) = Uni (FreeMod coeff (U var))
  deriving (Eq,Ord,Show)

unUni :: Univariate c v -> FreeMod c (U v)
unUni (Uni a) = a

-- | An univariate polynomial integer coefficients
type ZUni var = Univariate Integer var

-- | An univariate polynomial with rational coefficients
type QUni var = Univariate Rational var

instance FreeModule (Univariate c v) where
  type BaseF  (Univariate c v) = U v 
  type CoeffF (Univariate c v) = c
  toFreeModule   = unUni
  fromFreeModule = Uni

-- | Name of the variable
uniVar :: KnownSymbol var => Univariate c var -> String
uniVar = symbolVal . varProxy where
  varProxy :: Univariate c var -> Proxy var
  varProxy _ = Proxy

renameUniVar :: Univariate c var1 -> Univariate c var2
renameUniVar = Unsafe.unsafeCoerce

--------------------------------------------------------------------------------

instance (Ring coeff, KnownSymbol var) => AlmostPolynomial (Univariate coeff var) where
                                          
  type CoeffP (Univariate coeff var) = coeff
  type MonomP (Univariate coeff var) = U var
  type VarP   (Univariate coeff var) = ()

  fromListP     = Uni . ZMod.fromList
  toListP       = ZMod.toList . unUni

  zeroP         = Uni ZMod.zero
  isZeroP       = ZMod.isZero . unUni
  oneP          = Uni (ZMod.generator emptyM)

  variableP     = Uni . ZMod.generator . variableM
  singletonP    = \v e -> Uni (ZMod.generator (singletonM v e))
  monomP        = \m     -> Uni $ ZMod.generator m
  scalarP       = \s     -> Uni $ ZMod.singleton emptyM s

  addP          = \p1 p2 -> Uni $ ZMod.add (unUni p1) (unUni p2)
  subP          = \p1 p2 -> Uni $ ZMod.sub (unUni p1) (unUni p2)
  negP          = Uni . ZMod.neg . unUni
  mulP          = \p1 p2 -> Uni $ ZMod.mulWith mulM (unUni p1) (unUni p2)
  productP      = \ps    -> Uni $ ZMod.productWith emptyM mulM $ map unUni ps

  coeffOfP      = \m p   -> ZMod.coeffOf m (unUni p)
  mulByMonomP   = \m p   -> Uni $ ZMod.mulByMonom  m (unUni p)
  scaleP        = \s p   -> Uni $ ZMod.scale s (unUni p) 

instance (Ring coeff, KnownSymbol var) => Polynomial (Univariate coeff var) where
  evalP         = \g f p -> let { !z = evalM f ; h (!m,!c) = g c * z m } in sum' $ map h $ ZMod.toList $ unUni p
  varSubsP      = \f p   -> Uni $ ZMod.mapBase (varSubsM f) (unUni p)
  coeffSubsP    = \f p   -> Uni $ ZMod.fromList $ map (termSubsM f) $ ZMod.toList $ unUni p 
  subsP         = \f p   -> Uni $ ZMod.flatMap (evalM (unUni . f)) (unUni p)

instance (Ring c, KnownSymbol v) => Num (Univariate c v) where
  fromInteger = scalarP . fromInteger
  (+)    = addP
  (-)    = subP
  negate = negP
  (*)    = mulP
  abs    = id
  signum = \_ -> scalarP 1

instance (Ring c, KnownSymbol v) => Pretty (Univariate c v) where
  pretty poly@(Uni fm) = if isSignedR (proxyCoeffP poly)
    then prettyFreeMod'  True   pretty fm
    else prettyFreeMod'' pretty pretty fm

-- hackety hack hack...
instance IsSigned (Univariate c v) where
  signOf = const (Just Plus)

-- So that we can use it again as a coefficient ring
instance (Ring c, KnownSymbol v) => Ring (Univariate c v) where
  isZeroR   = ZMod.isZero . unUni
  isAtomicR = const False
  isSignedR = const False
  absR      = id
  signumR   = const (Just Plus)

--------------------------------------------------------------------------------
