
-- | Multivariate compact monomials where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@. 
--
-- This is very similar to the \"Indexed\" version, but should have much more
-- compact in-memory representation (which is useful in case of large or many 
-- polynomials, and should be in theory also faster, because of cache friendlyness)
--

{-# LANGUAGE CPP, BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables #-}
module Math.Algebra.Polynomial.Monomial.Compact where

--------------------------------------------------------------------------------

import Data.List
import Data.Word

import Data.Array.Unboxed  -- used only by compactFromList

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

import qualified Data.Vector.Compact.WordVec as V

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

import Math.Algebra.Polynomial.Monomial.Indexed ( XS , xsFromExponents , xsToExponents )

--------------------------------------------------------------------------------
-- * Monomials

-- | Monomials of the variables @x1,x2,...,xn@. The internal representation is a
-- compact vector of the exponents.
--
-- The type is indexed by the /name/ of the variables, and then the /number/ of variables.
--
-- Note that we assume here that the internal vector has length @n@.
newtype Compact (var :: Symbol) (n :: Nat) 
  = Compact V.WordVec 
  deriving (Eq,Show,Typeable)

--------------------------------------------------------------------------------

-- note: this must be a monomial ordering!
instance Ord (Compact var n) where 
  compare (Compact a) (Compact b) = compare a b

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
      es = compactToWordExpoList monom
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

--------------------------------------------------------------------------------
-- * Conversion

-- | from @(variable,exponent)@ pairs
compactFromList :: KnownNat n => [(Index,Int)] -> Compact v n
compactFromList list = xs where
  xs  = Compact $ V.fromList {- n -} (elems arr)
  arr = accumArray (+) 0 (1,n) list' :: UArray Int Word
  n   = nOfCompact xs
  list' = map f list :: [(Int,Word)]
  f (Index j , e)
    | j < 1      = error "compactFromList: index out of bounds (too small)"
    | j > n      = error "compactFromList: index out of bounds (too big)"
    | e < 0      = error "compactFromList: negative exponent"
    | otherwise  = (j,fromIntegral e)
  
-- | to @(variable,exponent)@ pairs
compactToList :: Compact v n -> [(Index,Int)]
compactToList (Compact vec) = filter cond $ zipWith f [1..] (V.toList vec) where
  f j e = (Index j, fromIntegral e)
  cond (_,e) = e > 0

-- | from @Word@ exponent list
compactFromWordExpoList :: KnownNat n => [Word] -> Compact var n
compactFromWordExpoList ws = cpt where
  n   = nOfCompact cpt
  cpt = Compact vec
  vec = V.fromList {- n -} (take n (ws ++ repeat 0))

-- | to @Word@ exponent list
compactToWordExpoList :: Compact var n -> [Word]
compactToWordExpoList (Compact vec) = V.toList vec

-- | from @Int@ exponent list
compactFromExponents :: KnownNat n => [Int] -> Compact v n
compactFromExponents = compactFromWordExpoList . map fromIntegral

-- | to @Int@ exponent list
compactToExponents :: KnownNat n => Compact v n -> [Int]
compactToExponents = map fromIntegral . compactToWordExpoList

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
  xs = Compact $ V.fromList' (V.Shape n 4) (replicate n (0::Word))
  n  = nOfCompact xs

isEmptyCompact :: Compact v n -> Bool
isEmptyCompact monom@(Compact vec) = (V.maximum vec == 0)
  -- all (==0) (compactToWordExpoList monom)

--------------------------------------------------------------------------------
-- * normalization

isNormalCompact :: KnownNat n => Compact v n -> Bool
isNormalCompact cpt@(Compact vec) = nOfCompact cpt == V.vecLen vec

--------------------------------------------------------------------------------
-- * creation

variableCompact :: KnownNat n => Index -> Compact v n 
variableCompact idx = singletonCompact idx 1

singletonCompact :: KnownNat n => Index -> Int -> Compact v n 
singletonCompact (Index j) e0
  | j < 1     = error "singletonCompact: index out of bounds (too small)"
  | j > n     = error "singletonCompact: index out of bounds (too big)"
  | e < 0     = error "singletonCompact: negative exponent"
  | otherwise = cpt
  where
    e    = fromIntegral e0 :: Word
    list = replicate (j-1) 0 ++ e : replicate (n-j) 0
    n    = nOfCompact cpt
    cpt  = Compact $ V.fromList' (V.Shape n (V.bitsNeededFor e)) list

--------------------------------------------------------------------------------
-- * products

mulCompact :: KnownNat n => Compact v n -> Compact v n -> Compact v n
mulCompact (Compact vec1) (Compact vec2) = Compact $ V.add vec1 vec2

productCompact :: (KnownNat n, Foldable f) => f (Compact v n) -> Compact v n
productCompact = F.foldl' mulCompact emptyCompact 

powCompact :: KnownNat n => Compact v n -> Int -> Compact v n
powCompact (Compact vec) e 
  | e < 0     = error "powCompact: negative exponent"
  | e == 0    = emptyCompact
  | otherwise = Compact $ V.scale (fromIntegral e) vec
  
divCompact :: KnownNat n => Compact v n -> Compact v n -> Maybe (Compact v n)
divCompact (Compact vec1) (Compact vec2) = Compact <$> V.subtract vec1 vec2

--------------------------------------------------------------------------------
-- * degree

maxDegCompact :: Compact v n -> Int
maxDegCompact (Compact vec) = fromIntegral (V.maximum vec)

totalDegCompact :: Compact v n -> Int
totalDegCompact (Compact vec) = fromIntegral (V.sum vec)

--------------------------------------------------------------------------------
-- * differentiation

diffCompact :: Num c => Index -> Int -> Compact v n -> Maybe (Compact v n, c)
diffCompact = error "diffCompact: not implemented yet"

{-
diffCompact :: Num c => Index -> Int -> Compact v n -> Maybe (Compact v n, c)
diffCompact _         0 cpt          = Just (cpt,1)
diffCompact (Index j) k (Compact ba) =
  if k8 > m8
    then Nothing
    else Just (Compact ba' , fromInteger c) 
  where
    k8   = fromIntegral k :: Word8
    m8   = indexByteArray ba (j-1) :: Word8
    m    = fromIntegral m8 :: Int
    ba'  = byteArrayFromList $ change $ byteArrayToList ba
    c    = product [ fromIntegral (m - i) | i<-[0..k-1] ] :: Integer
    change = go 1 where
      go i (x:xs) = if i == j then (x-k8) : xs else x : go (i+1) xs
      go i []     = [] 
-}

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
  divM       = divCompact
  productM   = productCompact
  powM       = powCompact 
  maxDegM    = maxDegCompact              
  totalDegM  = totalDegCompact
  diffM      = diffCompact
 
  evalM      = error "Compact/evalM: not yet implemented"
  varSubsM   = error "Compact/varSubsM: not yet implemented"
  termSubsM  = error "Compact/termSubsM: not yet implemented"

--------------------------------------------------------------------------------
