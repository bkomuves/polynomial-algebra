
-- | Exterior monomials where the variable set 
-- looks like @{x_1, x_2, ... , x_N}@ 
--
-- The internal representation is a bit vector

{-# LANGUAGE 
      CPP, BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables,
      FlexibleContexts
  #-}
module Math.Algebra.Polynomial.Monomial.Exterior.Indexed where

--------------------------------------------------------------------------------

import Data.Maybe
import Data.List
import Data.Array.Unboxed 
import Data.Ord
import Data.Bits

import Data.Typeable
import GHC.TypeLits
import Data.Proxy

import Data.Foldable as F 

import qualified Data.Set as Set ; import Data.Set (Set)   -- IntSet and
import qualified Data.Map as Map ; import Data.Map (Map)   -- IntMap would be more efficient

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

import Math.Algebra.Polynomial.FreeModule ( PartialMonoid(..) )

--------------------------------------------------------------------------------
-- * Exterior monomials

-- | Exterior monomials of the variables @x1,x2,...,xn@. The internal representation is 
-- a bit vector encoded as an @Integer@
newtype Ext (var :: Symbol) (n :: Nat) = Ext Integer deriving (Eq,Ord,Show)

-- | Signed exterior monomial
data SgnExt (var :: Symbol) (n :: Nat) = SgnExt !Sign !(Ext var n) deriving (Eq,Ord,Show)

unExt :: Ext v n -> Integer
unExt (Ext k) = k

instance KnownNat n => PartialMonoid (SgnExt var n) where
  pmUnit = emptySgnExt
  pmAdd  = mulSgnExt   

instance KnownSymbol var => Pretty (Ext var n) where 
  pretty monom =   
    case [ showX i | i <- extToList monom ] of 
      [] -> "(1)"
      xs -> intercalate "/\\" xs
    where
      v = extVar monom
      showX !(Index i) = v ++ show i

instance KnownSymbol var => Pretty (SgnExt var n) where 
  pretty (SgnExt sgn ext) = case sgn of
    Plus  -> '+' : pretty ext
    Minus -> '-' : pretty ext

-- | Name of the variables
extVar :: KnownSymbol var => Ext var n -> String
extVar = symbolVal . varProxy where
  varProxy :: Ext var n -> Proxy var
  varProxy _ = Proxy

-- | Number of variables
nOfExt :: KnownNat n => Ext var n -> Int
nOfExt = fromInteger . natVal . natProxy where
  natProxy :: Ext var n -> Proxy n
  natProxy _ = Proxy

nOfMbExt :: KnownNat n => Maybe (Ext var n) -> Int
nOfMbExt = fromInteger . natVal . natProxy where
  natProxy :: Maybe (Ext var n) -> Proxy n
  natProxy _ = Proxy

nOfSgnExt :: KnownNat n => SgnExt var n -> Int
nOfSgnExt = fromInteger . natVal . natProxy where
  natProxy :: SgnExt var n -> Proxy n
  natProxy _ = Proxy

nOfMbSgnExt :: KnownNat n => Maybe (SgnExt var n) -> Int
nOfMbSgnExt = fromInteger . natVal . natProxy where
  natProxy :: Maybe (SgnExt var n) -> Proxy n
  natProxy _ = Proxy

--------------------------------------------------------------------------------
-- * emptyness

emptyExt :: KnownNat n => Ext v n
emptyExt = Ext 0

emptySgnExt :: KnownNat n => SgnExt v n
emptySgnExt = SgnExt Plus (Ext 0)

isEmptyExt :: Ext v n -> Bool
isEmptyExt (Ext a) = (a==0)

--------------------------------------------------------------------------------
-- * normalization

isNormalExt :: KnownNat n => Ext v n -> Bool
isNormalExt ext@(Ext int) = shiftR int n == 0 where n = nOfExt ext

--------------------------------------------------------------------------------
-- * conversion

extFromList :: KnownNat n => [Index] -> Maybe (SgnExt v n)
extFromList list = result where
  result
    | Map.null multiset                     = Just emptySgnExt
    | fst (Map.findMin multiset) < Index 1  = error "extFromList: index out of bounds (too small)"
    | fst (Map.findMax multiset) > Index n  = Nothing  -- should this be an error ?
    | any (>1) (Map.elems multiset)         = Nothing
    | otherwise                             = Just (SgnExt sgn $ Ext int)
  n = nOfMbSgnExt result
  multiset = Map.fromListWith (+) [ (idx,1) | idx <- list ] 
  perm = sortingPermutationAsc list
  sgn = if odd (numberOfInversionsMerge perm) then Minus else Plus
  int = sum' [ shiftL 1 (j-1) | Index j <- Map.keys multiset ]

extToList :: Ext v n -> [Index]
extToList (Ext int) = go 0 int where
  go _   0 = []
  go !i !a = if testBit a 0 
    then Index (i+1) : go (i+1) (shiftR a 1)
    else               go (i+1) (shiftR a 1)

extFromSet :: KnownNat n => Set Index -> Maybe (Ext v n)
extFromSet set = result where
  n = nOfMbExt result
  result = case Set.lookupMax set of
    Nothing        -> Just emptyExt
    Just (Index k) -> if k > n
      then Nothing   -- should this be an error ?
      else if (Set.findMin set < Index 1)
        then error "extFromSet: index smaller than 1"
        else Just $ Ext $ sum' [ shiftL 1 (j-1) | Index j <- Set.toList set ]
  
extToSet :: Ext v n -> Set Index
extToSet = Set.fromList . extToList

--------------------------------------------------------------------------------
-- * creation

variableExt :: KnownNat n => Index -> Ext v n 
variableExt (Index idx) = Ext $ shiftL 1 (idx-1)

--------------------------------------------------------------------------------
-- * multiplication

mulExt :: KnownNat n => Ext v n -> Ext v n -> Maybe (SgnExt v n)
mulExt x y = extFromList (extToList x ++ extToList y)

mulExtCoeff :: (Num c, KnownNat n) => Ext v n -> Ext v n -> Maybe (Ext v n, c)
mulExtCoeff x y = case mulExt x y of
  Nothing             -> Nothing
  Just (SgnExt sgn z) -> case sgn of
    Plus  -> Just (z,  1)
    Minus -> Just (z, -1)

mulSgnExt :: KnownNat n => SgnExt v n -> SgnExt v n -> Maybe (SgnExt v n)
mulSgnExt (SgnExt s x) (SgnExt t y) = case mulExt x y of
  Nothing           -> Nothing
  Just (SgnExt u z) -> Just $ SgnExt (s `mappend` t `mappend` u) z

productExt :: (KnownNat n, Foldable f) => f (Ext v n) -> Maybe (SgnExt v n)
productExt t = go Plus (F.toList t) where
  go !sgn list = case list of
    []         -> Just (SgnExt sgn emptyExt)
    [x]        -> Just (SgnExt sgn x)
    (x:y:rest) -> case mulExt x y of
      Nothing           -> Nothing
      Just (SgnExt s z) -> go (sgn `mappend` s) (z:rest) 

--------------------------------------------------------------------------------

[v1,v2,v3,v4,v5,v6] = [ variableExt (Index i) | i<-[1..6] ] :: [Ext "a" 7]
Just a = productExt [v1,v2,v3]
Just b = productExt [v4,v5,v6]

prop_graded_anticomm :: KnownNat n => Ext v n -> Ext v n -> Bool
prop_graded_anticomm x y 
  | isNothing mb1 && isNothing mb2   = True
  | isJust    mb1 && isJust    mb2   = u == v && maybeFlip s == t
  | otherwise                        = False
  where
    mb1 = x `mulExt` y
    mb2 = y `mulExt` x
    Just (SgnExt s u) = mb1
    Just (SgnExt t v) = mb2
    d1 = degreeExt x
    d2 = degreeExt y
    maybeFlip = if odd (d1*d2) then oppositeSign else id    

prop_graded_anticomm_sgn :: KnownNat n => SgnExt v n -> SgnExt v n -> Bool
prop_graded_anticomm_sgn x y 
  | isNothing mb1 && isNothing mb2   = True
  | isJust    mb1 && isJust    mb2   = u == v && maybeFlip s == t
  | otherwise                        = False
  where
    mb1 = x `mulSgnExt` y
    mb2 = y `mulSgnExt` x
    Just (SgnExt s u) = mb1
    Just (SgnExt t v) = mb2
    d1 = degreeSgnExt x
    d2 = degreeSgnExt y
    maybeFlip = if odd (d1*d2) then oppositeSign else id    

--------------------------------------------------------------------------------
-- * degree

degreeExt :: Ext v n -> Int
degreeExt (Ext k) = popCount k

degreeSgnExt :: SgnExt v n -> Int
degreeSgnExt (SgnExt sgn ext) = degreeExt ext

--------------------------------------------------------------------------------
-- * Permutations

--
newtype Permutation = Permutation (UArray Int Int) deriving (Eq,Ord)

toPermutationUnsafe :: [Int] -> Permutation
toPermutationUnsafe xs = Permutation perm where
  n    = length xs
  perm = listArray (1,n) xs

sortingPermutationAsc :: Ord a => [a] -> Permutation
sortingPermutationAsc xs = toPermutationUnsafe (map fst sorted) where
  sorted = sortBy (comparing snd) $ zip [1..] xs

{-
isEvenPermutation :: Permutation -> Bool
isEvenPermutation (Permutation perm) = res where

  (1,n) = bounds perm
  res = runST $ do
    tag <- newArray (1,n) False 
    cycles <- unfoldM (step tag) 1 
    return $ even (sum cycles)
    
  step :: STUArray s Int Bool -> Int -> ST s (Int,Maybe Int)
  step tag k = do
    cyclen <- worker tag k k 0
    m <- next tag (k+1)
    return (cyclen,m)
    
  next :: STUArray s Int Bool -> Int -> ST s (Maybe Int)
  next tag k = if k > n
    then return Nothing
    else readArray tag k >>= \b -> if b 
      then next tag (k+1)  
      else return (Just k)
      
  worker :: STUArray s Int Bool -> Int -> Int -> Int -> ST s Int
  worker tag k l cyclen = do
    writeArray tag l True
    let m = perm ! l
    if m == k 
      then return cyclen
      else worker tag k m (1+cyclen)      
-}

isEvenPermutation :: Permutation -> Bool
isEvenPermutation = even . numberOfInversionsMerge

-- | Returns the number of inversions, using the merge-sort algorithm.
-- This should be @O(n*log(n))@
--
numberOfInversionsMerge :: Permutation -> Int
numberOfInversionsMerge (Permutation arr) = fst (sortCnt n $ elems arr) where
  (_,n) = bounds arr
                                        
  -- | First argument is length of the list.
  -- Returns also the inversion count.
  sortCnt :: Int -> [Int] -> (Int,[Int])
  sortCnt 0 _     = (0,[] )
  sortCnt 1 [x]   = (0,[x])
  sortCnt 2 [x,y] = if x>y then (1,[y,x]) else (0,[x,y])
  sortCnt n xs    = mergeCnt (sortCnt k us) (sortCnt l vs) where
    k = div n 2
    l = n - k 
    (us,vs) = splitAt k xs

  mergeCnt :: (Int,[Int]) -> (Int,[Int]) -> (Int,[Int])
  mergeCnt (!c,us) (!d,vs) = (c+d+e,ws) where

    (e,ws) = go 0 us vs 

    go !k xs [] = ( k*length xs , xs )
    go _  [] ys = ( 0 , ys)
    go !k xxs@(x:xs) yys@(y:ys) = if x < y
      then let (a,zs) = go  k     xs yys in (a+k, x:zs)
      else let (a,zs) = go (k+1) xxs  ys in (a  , y:zs)

--------------------------------------------------------------------------------
