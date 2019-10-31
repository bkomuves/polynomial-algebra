
-- | Multivariate polynomials where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@ 

{-# LANGUAGE 
      BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables,
      FlexibleContexts, StandaloneDeriving
  #-}
module Math.Algebra.Polynomial.Multivariate.Indexed
  (
    Poly(..) , unPoly , polyVar , nOfPoly
  , ZPoly , QPoly
  , embed
  , XS(..)
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

import Math.Algebra.Polynomial.Monomial.Indexed 

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------
-- * Polynomials

-- | A multivariate polynomial in with a given coefficient ring. 
--
-- It is also indexed by the (shared) /name/ of the variables and the /number of/
-- variable. For example @Polyn Rational "x" 3@ the type of polynomials in the
-- variables @x1, x2, x3@ with rational coefficients.
newtype Poly (coeff :: *) (var :: Symbol) (n :: Nat) 
  = Poly (FreeMod coeff (XS var n))
  deriving (Eq,Ord,Show,Typeable)

-- deriving instance (Ord coeff) => Ord (Poly coeff var n)

unPoly :: Poly c v n -> FreeMod c (XS v n) 
unPoly (Poly p) = p

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

--------------------------------------------------------------------------------

type ZPoly = Poly Integer
type QPoly = Poly Rational

--------------------------------------------------------------------------------

instance (Ring c, KnownSymbol v, KnownNat n) => Polynomial (Poly c v n) where
  type CoeffP (Poly c v n) = c
  type MonomP (Poly c v n) = XS v n
  type VarP   (Poly c v n) = Index

  zeroP         = Poly ZMod.zero
  isZeroP       = ZMod.isZero . unPoly
  oneP          = Poly (ZMod.generator emptyM)

  fromListP     = Poly . ZMod.fromList
  toListP       = ZMod.toList . unPoly

  variableP     = Poly . ZMod.generator . variableXS
  singletonP    = \v e -> Poly (ZMod.generator (singletonXS v e))
  monomP        = \m     -> Poly $ ZMod.generator m
  scalarP       = \s     -> Poly $ ZMod.singleton emptyXS s

  addP          = \p1 p2 -> Poly $ ZMod.add (unPoly p1) (unPoly p2)
  subP          = \p1 p2 -> Poly $ ZMod.sub (unPoly p1) (unPoly p2)
  negP          = Poly . ZMod.neg . unPoly
  mulP          = \p1 p2 -> Poly $ ZMod.mulWith     mulXS (unPoly p1) (unPoly p2)

  coeffOfP      = \m p   -> ZMod.coeffOf m (unPoly p)
  productP      = \ps    -> Poly $ ZMod.productWith emptyXS mulXS $ map unPoly ps
  mulByMonomP   = \m p   -> Poly $ ZMod.mulByMonom  m (unPoly p)
  scaleP        = \s p   -> Poly $ ZMod.scale s (unPoly p) 

  evalP         = \g f p -> let { !z = evalM f ; h (!m,!c) = g c * z m } in sum' $ map h $ ZMod.toList $ unPoly p
  varSubsP      = \f p   -> Poly $ ZMod.mapBase (varSubsM f) (unPoly p)
  coeffSubsP    = \f p   -> Poly $ ZMod.fromList $ map (termSubsM f) $ ZMod.toList $ unPoly p 
  subsP         = \f p   -> Poly $ ZMod.flatMap (evalM (unPoly . f)) (unPoly p)

instance (Ring c, KnownSymbol v, KnownNat n) => Num (Poly c v n) where
  fromInteger = scalarP . fromInteger
  (+)    = addP
  (-)    = subP
  negate = negP
  (*)    = mulP
  abs    = id
  signum = \_ -> scalarP 1

instance (Ring c, KnownSymbol v, KnownNat n, Pretty (XS v n)) => Pretty (Poly c v n) where
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

-- | You can always increase the number of variables; 
-- you can also decrease, if don't use the last few ones.
--
-- This will throw an error if you try to eliminate variables which are in fact used.
-- To do that, you can instead substitute 1 into them.
--
embed :: (Ring c, KnownNat n, KnownNat m) => Poly c v n -> Poly c v m
embed old@(Poly old_fm) = new where
  n = nOfPoly old
  m = nOfPoly new
  new = Poly $ case compare m n of 
    LT -> ZMod.mapBase project old_fm
    EQ -> ZMod.mapBase keep    old_fm
    GT -> ZMod.mapBase extend  old_fm
  extend  (XS arr) = XS $ listArray (1,m) (elems arr ++ replicate (m-n) 0)
  keep    (XS arr) = XS arr
  project (XS arr) = 
    let old = elems arr
        (new,rest) = splitAt m old
    in  if all (==0) rest 
          then XS $ listArray (1,m) new
          else error "Indexed/embed: the projected variables are actually used!"

--------------------------------------------------------------------------------
