
-- | Multivariate compact polynomials where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@, and the exponents are 
-- a priori known to be at most 255.  
--
-- This is very similar to the \"Indexed\" version, but should have much more
-- compact in-memory representation (which is useful in case of large or many 
-- polynomials,  and should be in theory also faster, because of cache issues)
--
-- WARNING! There are no checks on the exponents, the user should ensure
-- that they indeed never exceed 255!
--

{-# LANGUAGE CPP, BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Monomial.Compact where

--------------------------------------------------------------------------------

import Data.List
import Data.Word
import Data.Array.Unboxed       -- used by `compactFromList' only
import Data.Primitive.ByteArray

#if MIN_VERSION_base(4,11,0)        
import Data.Semigroup
import Data.Monoid
#else
import Data.Monoid
#endif

import Data.Typeable
import GHC.TypeLits
import Data.Proxy

import Data.Foldable as F 

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

import Math.Algebra.Polynomial.Monomial.Indexed ( XS , xsFromExponents , xsToExponents )

--------------------------------------------------------------------------------
-- * Monomials

-- | Monomials of the variables @x1,x2,...,xn@. The internal representation is a
-- dense byte array of the exponents.
--
-- The type is indexed by the /name/ of the variables, and then the /number/ of variables.
--
-- Note that we assume here that the internal ByteArray has length @n@.
newtype Compact (var :: Symbol) (n :: Nat) = Compact ByteArray deriving (Eq,Show,Typeable)

--------------------------------------------------------------------------------

-- because of how we encode it (list of exponents), the opposite order 
-- seems more natural for printing out terms (?)
instance Ord (Compact var n) where compare (Compact a) (Compact b) = compare b a

instance KnownNat n => Semigroup (Compact var n) where
  (<>) = mulCompact

instance KnownNat n => Monoid (Compact var n) where
  mempty  = emptyCompact
  mappend = mulCompact

instance KnownSymbol var => Pretty (Compact var n) where 
  pretty monom =   
    case [ showXPow i e | (i,e) <- zip [1..] es , e /= 0 ] of 
      [] -> "(1)"
      xs -> intercalate "*" xs
    where
      es = compactToExpoListW8 monom
      v  = compactVar monom
      showXPow !i !e = case e of
        0 -> "1"
        1 -> v ++ show i
        _ -> v ++ show i ++ "^" ++ show e

-- | Name of the variables
compactVar :: KnownSymbol var => Compact var n -> String
compactVar = symbolVal . varProxy where
  varProxy :: Compact var n -> Proxy var
  varProxy _ = Proxy

-- | Number of variables
nOfCompact :: KnownNat n => Compact var n -> Int
nOfCompact = fromInteger . natVal . natProxy where
  natProxy :: Compact var n -> Proxy n
  natProxy _ = Proxy

{-
-- | Number of variables
nOfZModCompact :: KnownNat n => FreeMod c (Compact var n) -> Int
nOfZModCompact = fromInteger . natVal . natProxy where
  natProxy :: FreeMod c (Compact var n) -> Proxy n
  natProxy _ = Proxy
-}

--------------------------------------------------------------------------------
-- * Conversion

-- | from @(variable,exponent)@ pairs
compactFromList :: KnownNat n => [(Index,Int)] -> Compact v n
compactFromList list = xs where
  xs  = Compact $ byteArrayFromListN n (elems arr)
  arr = accumArray (+) 0 (1,n) list' :: UArray Int Word8
  n   = nOfCompact xs
  list' = map f list :: [(Int,Word8)]
  f (Index j , e)
    | j < 1      = error "compactFromList: index out of bounds (too small)"
    | j > n      = error "compactFromList: index out of bounds (too big)"
    | e < 0      = error "compactFromList: negative exponent"
    | e > 255    = error "compactFromList: exponent too big (should be at most 255)"
    | otherwise  = (j,fromIntegral e)
  
-- | to @(variable,exponent)@ pairs
compactToList :: Compact v n -> [(Index,Int)]
compactToList (Compact ba) = zipWith f [1..] (byteArrayToList ba) where
  f j e = (Index j, fromIntegral e)

-- | from 'Word8' exponent list
compactFromExpoListW8 :: KnownNat n => [Word8] -> Compact var n
compactFromExpoListW8 ws = cpt where
  cpt = Compact ba
  n   = nOfCompact cpt
  ba  = byteArrayFromListN n (take n (ws ++ repeat 0))

-- | to 'Word8' exponent list
compactToExpoListW8 :: Compact var n -> [Word8]
compactToExpoListW8 (Compact ba) = byteArrayToList ba

-- | from @Int@ exponent list
compactFromExponents :: KnownNat n => [Int] -> Compact v n
compactFromExponents = compactFromExpoListW8 . map fromIntegral

-- | to @Int@ exponent list
compactToExponents :: KnownNat n => Compact v n -> [Int]
compactToExponents = map fromIntegral . compactToExpoListW8

-- | from 'XS' exponent list
compactFromXS :: KnownNat n => XS v n -> Compact v n 
compactFromXS = compactFromExponents . xsToExponents

-- | to 'XS' exponent list
compactToXS :: KnownNat n => Compact v n -> XS v n
compactToXS = xsFromExponents . compactToExponents

--------------------------------------------------------------------------------
-- * empty (all zero exponents)

emptyCompact :: KnownNat n => Compact v n
emptyCompact = xs where 
  xs = Compact $ byteArrayFromListN n (replicate n (0::Word8))
  n  = nOfCompact xs

isEmptyCompact :: Compact v n -> Bool
isEmptyCompact monom = all (==0) (compactToExpoListW8 monom)

--------------------------------------------------------------------------------
-- * normalization

isNormalCompact :: KnownNat n => Compact v n -> Bool
isNormalCompact cpt@(Compact ba) = nOfCompact cpt == sizeofByteArray ba

--------------------------------------------------------------------------------
-- * creation

variableCompact :: KnownNat n => Index -> Compact v n 
variableCompact idx = singletonCompact idx 1

singletonCompact :: KnownNat n => Index -> Int -> Compact v n 
singletonCompact (Index j) e 
  | j < 1     = error "singletonCompact: index out of bounds (too small)"
  | j > n     = error "singletonCompact: index out of bounds (too big)"
  | e < 0     = error "singletonCompact: negative exponent"
  | e > 255   = error "singletonCompact: exponent too big (should be at most 255)"
  | otherwise = cpt
  where
    list = replicate j 0 ++ (fromIntegral e :: Word8) : replicate (n-j-1) 0
    n    = nOfCompact cpt
    cpt  = Compact $ byteArrayFromListN n list

--------------------------------------------------------------------------------
-- * products

mulCompact :: KnownNat n => Compact v n -> Compact v n -> Compact v n
mulCompact (Compact ba1) (Compact ba2) = Compact (addByteArrays ba1 ba2) 

productCompact :: (KnownNat n, Foldable f) => f (Compact v n) -> Compact v n
productCompact = F.foldl' mulCompact emptyCompact 

powCompact :: KnownNat n => Compact v n -> Int -> Compact v n
powCompact (Compact ba) e 
  | e < 0     = error "powCompact: negative exponent"
  | e == 0    = emptyCompact
  | otherwise = Compact $ mapByteArray (*e8) ba where e8 = (fromIntegral e :: Word8)

--------------------------------------------------------------------------------
-- * degree

maxdegCompact :: Compact v n -> Int
maxdegCompact (Compact ba) = fromIntegral (maxByteArray ba)

totaldegCompact :: Compact v n -> Int
totaldegCompact (Compact ba) = sumByteArray ba

--------------------------------------------------------------------------------

instance (KnownNat n, KnownSymbol v) => Monomial (Compact v n) where
  type VarM (Compact v n) = Index
  normalizeM = id
  isNormalM  = isNormalCompact
  fromListM  = compactFromList
  toListM    = compactToList
  emptyM     = emptyCompact
  isEmptyM   = isEmptyCompact
  variableM  = variableCompact
  singletonM = singletonCompact
  mulM       = mulCompact
  productM   = productCompact
  powM       = powCompact
  maxDegM    = maxdegCompact              
  totalDegM  = totaldegCompact

--------------------------------------------------------------------------------
-- * ByteArray helpers

byteArrayToList :: ByteArray -> [Word8]
byteArrayToList ba = [ indexByteArray ba i | i<-[0..n-1] ] where
  n = sizeofByteArray ba

mapByteArray :: (Word8 -> Word8) -> ByteArray -> ByteArray
mapByteArray f ba = byteArrayFromListN n (map f $ byteArrayToList ba) where
  n = sizeofByteArray ba

-- | We assume that the lengths are the same!
addByteArrays :: ByteArray -> ByteArray -> ByteArray 
addByteArrays ba1 ba2 = ba3 where
  ba3 = byteArrayFromListN n 
          [ indexByteArray ba1 i + (indexByteArray ba2 i :: Word8) | i<-[0..n-1] ]
  n = sizeofByteArray ba1

maxByteArray :: ByteArray -> Word8
maxByteArray = foldrByteArray (max :: Word8 -> Word8 -> Word8) 0 

sumByteArray :: ByteArray -> Int 
sumByteArray = foldrByteArray f 0 where
  f :: Word8 -> Int -> Int
  f w i = i + (fromIntegral w :: Int)

--------------------------------------------------------------------------------
