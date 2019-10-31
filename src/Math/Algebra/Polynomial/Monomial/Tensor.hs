
-- | Tensor product of polynomial algebras

{-# LANGUAGE CPP, BangPatterns, TypeFamilies, UnicodeSyntax #-}
module Math.Algebra.Polynomial.Monomial.Tensor where

--------------------------------------------------------------------------------

import Data.Typeable
import Data.Either

#if MIN_VERSION_base(4,11,0)        
import Data.Semigroup
import Data.Monoid
#else
import Data.Monoid
#endif

import Math.Algebra.Polynomial.Class
import Math.Algebra.Polynomial.Pretty

--------------------------------------------------------------------------------

data Tensor a b = Tensor !a !b deriving (Eq,Ord,Show,Typeable)

instance (Semigroup a, Semigroup b) => Semigroup (Tensor a b) where
  (<>) (Tensor x1 y1) (Tensor x2 y2) = Tensor (x1<>x2) (y1<>y2)
  
instance (Monoid a, Monoid b) => Monoid (Tensor a b) where
  mempty = Tensor mempty mempty
  mappend (Tensor x1 y1) (Tensor x2 y2) = Tensor (x1 `mappend` x2) (y1 `mappend` y2)

instance (Pretty a, Pretty b) => Pretty (Tensor a b) where
  pretty (Tensor a b) = pretty a ++ " `otimes` " ++ pretty b
  
--------------------------------------------------------------------------------
-- * Injections

injLeft :: Monoid b => a -> Tensor a b
injLeft x = Tensor x mempty

injRight :: Monoid a => b -> Tensor a b
injRight x = Tensor mempty x

--------------------------------------------------------------------------------
-- * Projections

projLeft :: Tensor a b -> a
projLeft (Tensor x _) = x

projRight :: Tensor a b -> b
projRight (Tensor _ y) = y

--------------------------------------------------------------------------------

instance (Monomial a, Monomial b) => Monomial (Tensor a b) where
  type VarM (Tensor a b) = Either (VarM a) (VarM b)
  
  -- checking the invariant
  normalizeM  (Tensor x y) = Tensor (normalizeM x) (normalizeM y)
  isNormalM   (Tensor x y) = isNormalM x && isNormalM y

  -- construction and deconstruction
  fromListM   list = Tensor (fromListM list1) (fromListM list2) where
                (list1,list2) = partitionEithers $ map distEither list                                         
  toListM     (Tensor x y) = map f (toListM x) ++ map g (toListM y) where
                f (v,e) = (Left  v, e)
                g (v,e) = (Right v, e)

  -- simple monomials
  emptyM      = Tensor emptyM emptyM
  isEmptyM    (Tensor x y) = isEmptyM x && isEmptyM y
  variableM   ei = case ei of 
                       Left  v -> Tensor (variableM v) emptyM
                       Right v -> Tensor emptyM (variableM v)
  singletonM  ei k = case ei of 
                       Left  v -> Tensor (singletonM v k) emptyM
                       Right v -> Tensor emptyM (singletonM v k)
  -- algebra
  mulM        (Tensor x1 y1) (Tensor x2 y2) = Tensor (mulM x1 x2) (mulM y1 y2)
  productM    tensors = Tensor (productM $ map projLeft tensors) (productM $ map projRight tensors)
  powM        (Tensor x y) k = Tensor (powM x k) (powM y k)

  -- degrees
  maxDegM     (Tensor x y) = max (maxDegM x) (maxDegM y)
  totalDegM   (Tensor x y) = totalDegM x + totalDegM y

  -- substitution and evaluation
  evalM       f (Tensor x y) = evalM (f . Left) x * evalM (f . Right) y
  varSubsM    f (Tensor x y) = Tensor x' y' where
                  x' = varSubsM (unsafeFromLeft  . f . Left ) x
                  y' = varSubsM (unsafeFromRight . f . Right) y
  termSubsM   f (Tensor x y, c) = (Tensor x' y', c*d*e) where
                  (x',d) = termSubsM (f . Left ) (x,1)
                  (y',e) = termSubsM (f . Right) (y,1)

--------------------------------------------------------------------------------
-- * Helpers

distEither :: (Either a b, c) -> Either (a,c) (b,c)
distEither (ei, z) = case ei of
  Left  x -> Left  (x,z)
  Right y -> Right (y,z)

unsafeFromLeft :: Either a b -> a
unsafeFromLeft ei = case ei of 
  Left  x -> x
  Right _ -> error "unsafeFromLeft: Right"

unsafeFromRight :: Either a b -> b
unsafeFromRight ei = case ei of 
  Left  _ -> error "unsafeFromRight: Left"
  Right y -> y

--------------------------------------------------------------------------------
