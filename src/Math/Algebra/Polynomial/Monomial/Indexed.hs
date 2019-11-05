
-- | Multivariate monomials where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@ 

{-# LANGUAGE 
      CPP, BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables,
      FlexibleContexts
  #-}
module Math.Algebra.Polynomial.Monomial.Indexed where

--------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import Data.Array.Unboxed 

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

--------------------------------------------------------------------------------
-- * Monomials

-- | Monomials of the variables @x1,x2,...,xn@. The internal representation is the
-- dense array of exponents: @x1^e1*x2^e2*...*xn^en@ is represented by @[e1,e2,...,en]@.
--
-- The type is indexed by the /name/ of the variables, and then the /number/ of variables.
--
-- Note that we require here that the array has bounds @(1,n)@
newtype XS (var :: Symbol) (n :: Nat) = XS (UArray Int Int) deriving (Eq,Show,Typeable)

-- | Note: this must be a monomial ordering!
instance Ord (XS var n) where compare (XS a) (XS b) = compare a b

instance KnownNat n => Semigroup (XS var n) where
  (<>) = mulXS

instance KnownNat n => Monoid (XS var n) where
  mempty  = emptyXS
  mappend = mulXS

instance KnownSymbol var => Pretty (XS var n) where 
  pretty monom@(XS arr) =   
    case [ showXPow i e | (i,e) <- zip [1..] es , e /= 0 ] of 
      [] -> "(1)"
      xs -> intercalate "*" xs
    where
      es = elems arr
      v = xsVar monom
      showXPow !i !e = case e of
        0 -> "1"
        1 -> v ++ show i
        _ -> v ++ show i ++ "^" ++ show e

-- | Name of the variables
xsVar :: KnownSymbol var => XS var n -> String
xsVar = symbolVal . varProxy where
  varProxy :: XS var n -> Proxy var
  varProxy _ = Proxy

-- | Number of variables
nOfXS :: KnownNat n => XS var n -> Int
nOfXS = fromInteger . natVal . natProxy where
  natProxy :: XS var n -> Proxy n
  natProxy _ = Proxy

--------------------------------------------------------------------------------
-- * emptyness

emptyXS :: KnownNat n => XS v n
emptyXS = xs where 
  xs = XS $ accumArray const 0 (1,n) []
  n  = nOfXS xs

isEmptyXS :: XS v n -> Bool
isEmptyXS (XS arr) = all (==0) (elems arr)

--------------------------------------------------------------------------------
-- * normalization

isNormalXS :: KnownNat n => XS v n -> Bool
isNormalXS xs@(XS arr) = bounds arr == (1,n) where n = nOfXS xs

--------------------------------------------------------------------------------
-- * conversion

-- | from @(variable,exponent)@ pairs
xsFromList :: KnownNat n => [(Index,Int)] -> XS v n
xsFromList list = xs where
  xs = XS $ accumArray (+) 0 (1,n) list'
  n  = nOfXS xs
  list' = map f list 
  f (Index j , e)
    | j < 1      = error "xsFromList: index out of bounds (too small)"
    | j > n      = error "xsFromList: index out of bounds (too big)"
    | e < 0      = error "xsFromList: negative exponent"
    | otherwise  = (j,e)
  
-- | to @(variable,exponent)@ pairs
xsToList :: XS v n -> [(Index,Int)]
xsToList (XS arr) = [ (Index j, e) | (j,e) <- assocs arr , e > 0 ]

--------------------------------------------------------------------------------

-- | from exponent list
xsFromExponents :: KnownNat n => [Int] -> XS v n
xsFromExponents expos = xs where
  xs   = XS $ listArray (1,n) list
  n    = nOfXS xs
  list = take n (expos ++ repeat 0)

-- | to exponent list
xsToExponents :: KnownNat n => XS v n -> [Int]
xsToExponents (XS arr) = elems arr

--------------------------------------------------------------------------------
-- * creation

variableXS :: KnownNat n => Index -> XS v n 
variableXS idx = singletonXS idx 1

singletonXS :: KnownNat n => Index -> Int -> XS v n 
singletonXS (Index j) e 
  | j < 1     = error "singletonXS: index out of bounds (too small)"
  | j > n     = error "singletonXS: index out of bounds (too big)"
  | e < 0     = error "singletonXS: negative exponent"
  | otherwise = xs
  where
    xs = XS $ accumArray (+) 0 (1,n) [(j,e)]
    n = nOfXS xs

--------------------------------------------------------------------------------
-- * multiplication

mulXS :: KnownNat n => XS v n -> XS v n -> XS v n
mulXS xs1@(XS es) (XS fs) = ys where
  ys = XS $ listArray (1,n) $ zipWith (+) (elems es) (elems fs) where
  n  = nOfXS xs1

productXS :: (KnownNat n, Foldable f) => f (XS v n) -> XS v n
productXS = F.foldl' mulXS emptyXS 

powXS :: XS v n -> Int -> XS v n
powXS (XS arr) e 
  | e < 0     = error "powXS: negative exponent"
  | e == 0    = XS (amap (const 0) arr)
  | otherwise = XS (amap (*e)      arr)

divXS :: KnownNat n => XS v n -> XS v n -> Maybe (XS v n)
divXS xs1@(XS es) (XS fs) 
  | all (>=0) gs  = Just (XS $ listArray (1,n) gs)
  | otherwise     = Nothing
  where
    gs = zipWith (-) (elems es) (elems fs) where
    n  = nOfXS xs1

--------------------------------------------------------------------------------
-- * degree

maxDegXS :: XS v n -> Int
maxDegXS (XS arr) = maximum (elems arr)

totalDegXS :: XS v n -> Int
totalDegXS (XS arr) = sum' (elems arr)

--------------------------------------------------------------------------------
-- * evaluation and substituion

evalXS :: Num c => (Index -> c) -> XS v n -> c
evalXS f xs@(XS arr) = foldl' (*) 1 (map g $ assocs arr) where
  g (!j,!e) = case e of
    0 -> 1
    1 -> f (Index j) 
    _ -> f (Index j) ^ e 

varSubsXS :: KnownNat n => (Index -> Index) -> XS v n -> XS v n
varSubsXS f xs@(XS arr) = XS arr' where
  n    = nOfXS xs
  arr' = accumArray (+) 0 (1,n) list
  list = [ ( myFromIndex (f (Index j)) , e ) | (j,e) <- assocs arr ]
  myFromIndex (Index j)  
    | j >= 1 && j <= 1  = j
    | otherwise         = error "varSubsXS: variable index out of bounds"

termSubsXS :: (KnownNat n, Num c) => (Index -> Maybe c) -> (XS v n, c) -> (XS v n, c) 
termSubsXS f (xs@(XS arr) , c0) = (XS arr', c0*proj) where
  n    = nOfXS xs
  arr' = accumArray (+) 0 (1,n) $ catMaybes mbs
  (proj,mbs)   = mapAccumL g 1 (assocs arr)
  g !s (!j,!e) = case f (Index j) of
    Nothing     -> (s       , Just (j,e) )
    Just c      -> (s * c^e , Nothing    )
  
--------------------------------------------------------------------------------

instance (KnownNat n, KnownSymbol v) => Monomial (XS v n) where
  type VarM (XS v n) = Index
  normalizeM  = id
  isNormalM   = isNormalXS
  fromListM   = xsFromList
  toListM     = xsToList
  emptyM      = emptyXS
  isEmptyM    = isEmptyXS
  variableM   = variableXS
  singletonM  = singletonXS
  mulM        = mulXS
  divM        = divXS
  productM    = productXS
  powM        = powXS
  maxDegM     = maxDegXS              
  totalDegM   = totalDegXS
  evalM       = evalXS
  varSubsM    = varSubsXS
  termSubsM   = termSubsXS

--------------------------------------------------------------------------------
-- * changing the number of variables

-- | You can always increase the number of variables; 
-- you can also decrease, if don't use the last few ones.
--
-- This will throw an error if you try to eliminate variables which are in fact used.
-- To do that, you can instead substitute 1 into them.
--
embedXS :: (KnownNat n, KnownNat m) => XS v n -> XS v m 
embedXS old = new where
  n = nOfXS old
  m = nOfXS new
  new = case compare m n of 
    LT -> project old
    EQ -> keep    old
    GT -> extend  old
  extend  (XS arr) = XS $ listArray (1,m) (elems arr ++ replicate (m-n) 0)
  keep    (XS arr) = XS arr
  project (XS arr) = 
    let old = elems arr
        (new,rest) = splitAt m old
    in  if all (==0) rest 
          then XS $ listArray (1,m) new
          else error "Indexed/embed: the projected variables are actually used!"

--------------------------------------------------------------------------------
