
-- | Multivariate compact polynomials where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@.
--
-- This is very similar to the \"Indexed\" version, but should have much more
-- compact in-memory representation (which is useful in case of large or many 
-- polynomials; and should be in theory also faster, because of cache-friendlyness)
--
--

{-# LANGUAGE BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables, FlexibleContexts #-}
module Math.Algebra.Polynomial.Multivariate.Compact 
  ( Poly(..) , unPoly , polyVar , nOfPoly , renamePolyVar
  , ZPoly , QPoly , fromZPoly, fromQPoly
  , Compact
  )
  where

--------------------------------------------------------------------------------

import Data.List
import Data.Word

import Data.Typeable
import GHC.TypeLits
import Data.Proxy
import Unsafe.Coerce as Unsafe

import Data.Foldable as F 

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod , FreeModule(..) ) -- , ZMod , QMod )

import Math.Algebra.Polynomial.Monomial.Compact

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------

-- | A multivariate polynomial in with a given coefficient ring. 
--
-- It is also indexed by the (shared) /name/ of the variables and the /number of/
-- variable. For example @Polyn Rational "x" 3@ the type of polynomials in the
-- variables @x1, x2, x3@ with rational coefficients.
newtype Poly (coeff :: *) (var :: Symbol) (n :: Nat) = Poly (FreeMod coeff (Compact var n))
  deriving (Eq,Ord,Show,Typeable)

unPoly :: Poly c v n -> FreeMod c (Compact v n)
unPoly (Poly x) = x

-- | Name of the variables
polyVar :: KnownSymbol var => Poly c var n -> String
polyVar = symbolVal . varProxy where
  varProxy :: Poly c var n -> Proxy var
  varProxy _ = Proxy

-- | Number of variables
nOfPoly :: KnownNat n => Poly c var n -> Int
nOfPoly = fromInteger . natVal . natProxy where
  natProxy :: Poly c var n -> Proxy n
  natProxy _ = Proxy

instance FreeModule (Poly c v n) where
  type BaseF  (Poly c v n) = Compact v n
  type CoeffF (Poly c v n) = c
  toFreeModule   = unPoly
  fromFreeModule = Poly

-- | Rename the variables (zero cost)
renamePolyVar :: Poly c var1 n -> Poly c var2 n
renamePolyVar = Unsafe.unsafeCoerce

--------------------------------------------------------------------------------

type ZPoly = Poly Integer
type QPoly = Poly Rational

-- | Change the coefficient ring (from integers)
fromZPoly :: (Ring c, KnownSymbol v, KnownNat n) => Poly Integer v n -> Poly c v n
fromZPoly= Poly . ZMod.fromZMod . unPoly

-- | Change the coefficient field (from rationals)
fromQPoly :: (Field c, KnownSymbol v, KnownNat n) => Poly Rational v n -> Poly c v n
fromQPoly = Poly . ZMod.fromQMod . unPoly

--------------------------------------------------------------------------------

instance (Ring c, KnownSymbol v, KnownNat n) => AlmostPolynomial (Poly c v n) where
  type CoeffP (Poly c v n) = c
  type MonomP (Poly c v n) = Compact v n
  type VarP   (Poly c v n) = Index

  zeroP         = Poly ZMod.zero
  isZeroP       = ZMod.isZero . unPoly
  oneP          = Poly (ZMod.generator emptyCompact)

  fromListP     = Poly . ZMod.fromList
  toListP       = ZMod.toList . unPoly

  variableP     = Poly . ZMod.generator . variableCompact
  singletonP    = \v e -> Poly (ZMod.generator (singletonCompact v e))
  monomP        = \m     -> Poly $ ZMod.generator m
  monomP'       = \m c   -> Poly $ ZMod.singleton m c
  scalarP       = \s     -> Poly $ ZMod.singleton emptyCompact s

  addP          = \p1 p2 -> Poly $ ZMod.add (unPoly p1) (unPoly p2)
  subP          = \p1 p2 -> Poly $ ZMod.sub (unPoly p1) (unPoly p2)
  negP          = Poly . ZMod.neg . unPoly
  mulP          = \p1 p2 -> Poly $ ZMod.mulWith     mulCompact (unPoly p1) (unPoly p2)

  coeffOfP      = \m p   -> ZMod.coeffOf m (unPoly p)
  productP      = \ps    -> Poly $ ZMod.productWith emptyCompact mulCompact $ map unPoly ps
  mulByMonomP   = \m p   -> Poly $ ZMod.mulByMonom  m (unPoly p)
  scaleP        = \s p   -> Poly $ ZMod.scale s (unPoly p) 

instance (Ring c, KnownSymbol v, KnownNat n) => Polynomial (Poly c v n) where
  evalP         = \g f p -> let { !z = evalM f ; h (!m,!c) = g c * z m } in sum' $ map h $ ZMod.toList $ unPoly p
  --varSubsP      = \f p   -> Poly $ ZMod.mapBase (varSubsCompact f) (unPoly p)
  --coeffSubsP    = \f p   -> Poly $ ZMod.fromList $ map (termSubsCompact f) $ ZMod.toList $ unPoly p 
  --subsP         = \f p   -> Poly $ ZMod.flatMap (evalCompact (unPoly . f)) (unPoly p)
  varSubsP   = error "Compact/varSubsP: not yet implemented"
  coeffSubsP = error "Compact/coeffSubsP: not yet implemented"
  subsP      = error "Compact/subsP: not yet implemented"
  

instance (Ring c, KnownSymbol v, KnownNat n) => Num (Poly c v n) where
  fromInteger = scalarP . fromInteger
  (+)    = addP
  (-)    = subP
  negate = negP
  (*)    = mulP
  abs    = id
  signum = \_ -> scalarP 1

instance (Ring c, KnownSymbol v, KnownNat n, Pretty (Compact v n)) => Pretty (Poly c v n) where
  pretty poly@(Poly fm) = if isSignedR (proxyCoeffP poly)
    then prettyFreeMod'  True   pretty fm
    else prettyFreeMod'' pretty pretty fm

-- hackety hack hack...
instance IsSigned (Poly c v n) where
  signOf = const (Just Plus)

-- So that we can use it again as a coefficient ring
instance (Ring c, KnownSymbol v, KnownNat n) => Ring (Poly c v n) where
  isZeroR   = ZMod.isZero . unPoly
  isAtomicR = const False
  isSignedR = const False
  absR      = id
  signumR   = const (Just Plus)

--------------------------------------------------------------------------------
