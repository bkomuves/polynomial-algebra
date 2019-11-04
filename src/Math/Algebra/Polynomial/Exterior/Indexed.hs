
-- | Exterior algebra where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@ 
--
-- See <https://en.wikipedia.org/wiki/Exterior_algebra>

{-# LANGUAGE 
      BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables,
      FlexibleContexts, StandaloneDeriving
  #-}
module Math.Algebra.Polynomial.Exterior.Indexed
  (
    ExtAlg(..) , unExtAlg , polyVar , nOfExtAlg
  , ZExtAlg , QExtAlg
  , embed
  , Ext(..)
  )
  where

--------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import Data.Array.Unboxed 

import Data.Typeable
import GHC.TypeLits
import Data.Proxy

import Data.Foldable as F 

import qualified Math.Algebra.Polynomial.FreeModule as ZMod
import Math.Algebra.Polynomial.FreeModule ( FreeMod ) -- , ZMod , QMod )

import Math.Algebra.Polynomial.Monomial.Exterior.Indexed 

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------
-- * Exterior algebra

-- | An exterior polynomial in with a given coefficient ring. 
--
-- It is also indexed by the (shared) /name/ of the variables and the /number of/
-- variable. For example @ExtAlgn Rational "x" 3@ the type of polynomials in the
-- variables @x1, x2, x3@ with rational coefficients.
newtype ExtAlg (coeff :: *) (var :: Symbol) (n :: Nat) 
  = ExtAlg (FreeMod coeff (Ext var n))
  deriving (Eq,Ord,Show,Typeable)

-- deriving instance (Ord coeff) => Ord (ExtAlg coeff var n)

unExtAlg :: ExtAlg c v n -> FreeMod c (Ext v n) 
unExtAlg (ExtAlg p) = p

-- | Name of the variables
polyVar :: KnownSymbol var => ExtAlg c var n -> String
polyVar = symbolVal . varProxy where
  varProxy :: ExtAlg c var n -> Proxy var
  varProxy _ = Proxy

-- | Number of variables
nOfExtAlg :: KnownNat n => ExtAlg c var n -> Int
nOfExtAlg = fromInteger . natVal . natProxy where
  natProxy :: ExtAlg c var n -> Proxy n
  natProxy _ = Proxy

--------------------------------------------------------------------------------

type ZExtAlg = ExtAlg Integer
type QExtAlg = ExtAlg Rational

--------------------------------------------------------------------------------

instance (Ring c, KnownSymbol v, KnownNat n) => AlmostPolynomial (ExtAlg c v n) where
  type CoeffP (ExtAlg c v n) = c
  type MonomP (ExtAlg c v n) = Ext v n
  type VarP   (ExtAlg c v n) = Index

  zeroP         = ExtAlg ZMod.zero
  isZeroP       = ZMod.isZero . unExtAlg
  oneP          = ExtAlg (ZMod.generator emptyExt)

  fromListP     = ExtAlg . ZMod.fromList
  toListP       = ZMod.toList . unExtAlg

  variableP     = ExtAlg . ZMod.generator . variableExt
  singletonP    = error "ExtAlg/singletonP: not implemented (because it is meaningless)"
  monomP        = \m     -> ExtAlg $ ZMod.generator m
  scalarP       = \s     -> ExtAlg $ ZMod.singleton emptyExt s

  addP          = \p1 p2 -> ExtAlg $ ZMod.add (unExtAlg p1) (unExtAlg p2)
  subP          = \p1 p2 -> ExtAlg $ ZMod.sub (unExtAlg p1) (unExtAlg p2)
  negP          = ExtAlg . ZMod.neg . unExtAlg
  mulP          = \p1 p2 -> ExtAlg $ ZMod.mulWith'' mulExtCoeff (unExtAlg p1) (unExtAlg p2)

  coeffOfP      = \m p   -> ZMod.coeffOf m (unExtAlg p)
  productP      = \ps    -> ExtAlg $ ZMod.productWith'' emptyExt mulExtCoeff $ map unExtAlg ps
  mulByMonomP   = \m p   -> ExtAlg $ ZMod.mapMaybeBaseCoeff (mulExtCoeff m) (unExtAlg p)    -- not injective!!!
  scaleP        = \s p   -> ExtAlg $ ZMod.scale s (unExtAlg p) 

{-
  evalP      = error "ExtAlg/evalP: not implemented"
  varSubsP   = error "ExtAlg/varSubsP: not implemented"
  coeffSubsP = error "ExtAlg/coeffSubsP: not implemented"
  subsP      = error "ExtAlg/subsP: not implemented"
-}


instance (Ring c, KnownSymbol v, KnownNat n) => Num (ExtAlg c v n) where
  fromInteger = scalarP . fromInteger
  (+)    = addP
  (-)    = subP
  negate = negP
  (*)    = mulP
  abs    = id
  signum = \_ -> scalarP 1

instance (Ring c, KnownSymbol v, KnownNat n, Pretty (Ext v n)) => Pretty (ExtAlg c v n) where
  pretty poly@(ExtAlg fm) = if isSignedR (proxyCoeffP poly)
    then prettyFreeMod'  True   pretty fm
    else prettyFreeMod'' pretty pretty fm

-- hackety hack hack...
instance IsSigned (ExtAlg c v n) where
  signOf = const (Just Plus)

-- So that we can use it again as a coefficient ring
instance (Ring c, KnownSymbol v, KnownNat n) => Ring (ExtAlg c v n) where
  isZeroR   = ZMod.isZero . unExtAlg
  isAtomicR = const False
  isSignedR = const False
  absR      = id
  signumR   = const (Just Plus)

--------------------------------------------------------------------------------

-- | You can always increase the number of variables; 
-- you can also decrease, if don't use the last few ones.
--
-- This will throw an error if you try to eliminate variables which are in fact used.
-- To do that, you can instead substitute 1 or 0 into them.
--
embed :: (Ring c, KnownNat n, KnownNat m) => ExtAlg c v n -> ExtAlg c v m
embed old@(ExtAlg old_fm) = new where
  n = nOfExtAlg old
  m = nOfExtAlg new
  new = ExtAlg $ case compare m n of 
    LT -> ZMod.unsafeMapBase project old_fm
    EQ -> ZMod.unsafeMapBase keep    old_fm
    GT -> ZMod.unsafeMapBase extend  old_fm
  extend  (Ext int) = Ext int
  keep    (Ext int) = Ext int
  project (Ext int) = let new = Ext int 
                      in  if isNormalExt new 
                            then new
                            else error "Exterior/Indexed/embed: the projected variables are actually used!"

--------------------------------------------------------------------------------
