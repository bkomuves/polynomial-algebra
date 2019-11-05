
-- | Multivariate monomials where the variable set is the countable infinite 
-- set @{x_1, x_2, x_3,... }@ 

{-# LANGUAGE 
      CPP, BangPatterns, TypeFamilies, DataKinds, KindSignatures, ScopedTypeVariables,
      FlexibleContexts
  #-}
module Math.Algebra.Polynomial.Monomial.Infinite where

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

import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------
-- * Monomials

-- | Monomials of the variables @x1,x2,x3,...@. The internal representation is a
-- list of exponents: @x1^e1*x2^e2*x3^e3...@ is represented by @[e1,e2,e3,...]@.
--
-- We assume that only finitely many nonzero exponents appear.
--
-- The type is indexed by the /name/ of the variables.
--
newtype XInf (var :: Symbol) = XInf [Int] deriving (Eq,Show,Typeable)

unXInf :: XInf var -> [Int]
unXInf (XInf ns) = ns

-- The opposite order does not makes sense here...
instance Ord (XInf var) where compare (XInf a) (XInf b) = compare a b

instance Semigroup (XInf var) where
  (<>) = mulXInf

instance Monoid (XInf var) where
  mempty  = emptyXInf
  mappend = mulXInf

instance KnownSymbol var => Pretty (XInf var) where 
  pretty monom@(XInf es) =   
    case [ showXPow i e | (i,e) <- zip [1..] es , e /= 0 ] of 
      [] -> "(1)"
      xs -> intercalate "*" xs
    where
      v  = xInfVar monom
      showXPow !i !e = case e of
        0 -> "1"
        1 -> v ++ show i
        _ -> v ++ show i ++ "^" ++ show e

-- | Name of the variables
xInfVar :: KnownSymbol var => XInf var -> String
xInfVar = symbolVal . varProxy where
  varProxy :: XInf var -> Proxy var
  varProxy _ = Proxy

--------------------------------------------------------------------------------

emptyXInf :: XInf v
emptyXInf = XInf []

isEmptyXInf :: XInf v -> Bool
isEmptyXInf (XInf arr) = all (==0) arr

mulXInf :: XInf v -> XInf v -> XInf v
mulXInf (XInf es) (XInf fs) = XInf $ longZipWith id id (+) es fs

productXInf :: (Foldable f) => f (XInf v) -> XInf v
productXInf = F.foldl' mulXInf emptyXInf 

divXInf :: XInf v -> XInf v -> Maybe (XInf v)
divXInf xs1@(XInf es) (XInf fs) 
  | all (>=0) gs  = Just (XInf gs)
  | otherwise     = Nothing
  where
    gs = longZipWith id negate (-) es fs where

--------------------------------------------------------------------------------

xInfFromList :: [(Index,Int)] -> XInf v
xInfFromList list = 
  case Map.lookupMax table of
    Nothing    -> XInf []
    Just (n,_) -> XInf [ Map.findWithDefault 0 i table | i<-[Index 1 .. n] ]
  where
    table = Map.fromListWith (+) list
  
xInfToList :: XInf v -> [(Index,Int)]
xInfToList (XInf arr) 
  = filter cond 
  $ zip [ Index j | j<-[1..] ] arr 
  where
    cond (_,e) = e > 0

xInfToMap :: XInf var -> Map Index Int
xInfToMap = Map.fromList . xInfToList

--------------------------------------------------------------------------------

normalizeXInf :: XInf v -> XInf v
normalizeXInf (XInf arr) = XInf $ reverse $ dropWhile (==0) $ reverse arr

isNormalXInf :: XInf v -> Bool
isNormalXInf (XInf arr) = null (takeWhile (==0) $ reverse arr) 

--------------------------------------------------------------------------------

variableXInf :: Index -> XInf v 
variableXInf idx = singletonXInf idx 1

singletonXInf :: Index -> Int -> XInf v 
singletonXInf (Index j) e 
  | j < 1     = error "singletonXInf: index out of bounds (smaller than 1)"
  | e < 0     = error "singletonXInf: negative exponent"
  | otherwise = XInf $ replicate (j-1) 0 ++ [e]

--------------------------------------------------------------------------------

powXInf :: XInf v -> Int -> XInf v
powXInf (XInf arr) e 
  | e < 0     = error "powXInf: negative exponent"
  | e == 0    = XInf []
  | otherwise = XInf (map (*e)      arr)

--------------------------------------------------------------------------------

maxDegXInf :: XInf v -> Int
maxDegXInf (XInf arr) = maximum arr

totalDegXInf :: XInf v -> Int
totalDegXInf (XInf arr) = sum' arr

--------------------------------------------------------------------------------

evalXInf :: Num c => (Index -> c) -> XInf v -> c
evalXInf f xinf = foldl' (*) 1 (map g $ xInfToList xinf) where
  g (!j,!e) = case e of
    0 ->  1
    1 ->  f j 
    _ -> (f j) ^ e 

varSubsXInf :: (Index -> Index) -> XInf v -> XInf v
varSubsXInf f xinf = new where
  table = xInfToMap xinf
  new   = xInfFromList [ (f v , e) | (v,e) <- Map.assocs table ] 
  -- NOTE: ^^^^^^^^ xInfFromList handles repeated variables!

termSubsXInf :: (Num c) => (Index -> Maybe c) -> (XInf v, c) -> (XInf v, c) 
termSubsXInf f (xinf, c0) = (xInfFromList list, c1) where
  (list,c1) = foldl' g ([],c0) (xInfToList xinf)
  g (old,c) (v,e) = case f v of
      Just d  -> (old , c * d^e)
      Nothing -> ((v,e):old , c)
  
--------------------------------------------------------------------------------
-- * differentiation
 
diffXInf :: Num c => Index -> Int -> XInf v -> Maybe (XInf v, c)
diffXInf _         0 xinf      = Just (xinf,1)
diffXInf (Index j) k (XInf es) =
  if k > m 
    then Nothing
    else Just (XInf es' , fromInteger c) 
  where
    m    = (es ++ repeat 0) !! (j-1)
    es'  = longReplaceListElem 0 (j-1) (m-k) es
    c    = product [ fromIntegral (m-i) | i<-[0..k-1] ] :: Integer

--------------------------------------------------------------------------------

instance (KnownSymbol v) => Monomial (XInf v) where
  type VarM (XInf v) = Index
  normalizeM  = normalizeXInf
  isNormalM   = isNormalXInf
  fromListM   = xInfFromList
  toListM     = xInfToList
  emptyM      = emptyXInf
  isEmptyM    = isEmptyXInf
  variableM   = variableXInf
  singletonM  = singletonXInf
  mulM        = mulXInf
  divM        = divXInf
  productM    = productXInf
  powM        = powXInf
  diffM       = diffXInf
  maxDegM     = maxDegXInf              
  totalDegM   = totalDegXInf
  evalM       = evalXInf
  varSubsM    = varSubsXInf
  termSubsM   = termSubsXInf

--------------------------------------------------------------------------------

