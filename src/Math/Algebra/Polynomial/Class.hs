
{-# LANGUAGE 
      FlexibleContexts, TypeFamilies, TypeSynonymInstances, FlexibleInstances, 
      GeneralizedNewtypeDeriving, ConstraintKinds
  #-}

module Math.Algebra.Polynomial.Class where

--------------------------------------------------------------------------------

import Data.List ( foldl' , foldl1' , maximum , null )
import Data.Typeable
import Data.Proxy

import Math.Algebra.Polynomial.Misc
import Math.Algebra.Polynomial.Pretty
import Math.Algebra.Polynomial.FreeModule ( FreeModule(..) ) 

--------------------------------------------------------------------------------
-- * Indices

-- | The index of a variable. This will be used as the variable type 
-- when the set of variables is a continguous set like @{x_1, x_2, ... , x_N}@ 
newtype Index 
  = Index Int 
  deriving (Eq,Ord,Show,Enum)

fromIndex :: Index -> Int
fromIndex (Index j) = j

instance Pretty Index where
  pretty (Index j) = "x_" ++ show j

--------------------------------------------------------------------------------
-- * Rings

-- | The class of coefficient rings. 
--
-- Since base rings like integers or rational behave differently than say
-- another polynomial ring as a coefficient ring, we have to be explicit
-- about some things (mainly for pretty-printing purposes
--
-- TODO: clean this up!
class (Eq c, Ord c, Num c, IsSigned c, Show c, Pretty c, Typeable c) => Ring c where
  isZeroR   :: c -> Bool
  signumR   :: c -> Maybe Sign
  absR      :: c -> c
  isSignedR :: Proxy c -> Bool
  isAtomicR :: Proxy c -> Bool

  isZeroR   = (==0)
  signumR   = signOf
  absR      = abs
  isSignedR = const True
  isAtomicR = const True

instance Ring Int
instance Ring Integer
instance Ring Rational

-- | The class of coefficient fields (this is just a constraint synonym for now)
type Field c = (Ring c, Fractional c)

--------------------------------------------------------------------------------

-- | The class of types whose inhabitants can serve as variables
-- (this is just a constraint synonym for now)
type Variable v = (Ord v, Show v, Pretty v, Typeable v)

--------------------------------------------------------------------------------
-- * Monomials

-- | The class of (multivariate) monomials
-- 
-- The @Maybe@-s are there to allow truncated and exterior polynomial rings
class (Pretty m) => Monomial m where
  -- | the type of variables
  type VarM m :: *                          
  
  -- checking the invariant
  normalizeM  :: m -> m                         -- ^ enforce the invariant 
  isNormalM   :: m -> Bool                      -- ^ check the invariant
  -- construction and deconstruction
  fromListM   :: [(VarM m,Int)] -> m            -- ^ construction from @(variable,exponent)@ pairs
  toListM     :: m -> [(VarM m,Int)]            -- ^ extracting @(variable,exponent)@ pairs
  -- simple monomials
  emptyM      :: m                              -- ^ the empty monomial (corresponding to the polynomial 1)
  isEmptyM    :: m -> Bool                      -- ^ checks whether it is empty
  variableM   :: VarM m        -> m             -- ^ a single variable
  singletonM  :: VarM m -> Int -> m             -- ^ a single variable raised to a power
  -- algebra
  mulM        :: m -> m -> m                    -- ^ multiplication of monomials
  productM    :: [m] -> m                       -- ^ product of several monomials
  powM        :: m -> Int -> m                  -- ^ raising to a power
  divM        :: m -> m -> Maybe m              -- ^ division of monomials
  -- calculus
  diffM       :: Num c => VarM m -> Int -> m -> Maybe (m,c)       -- ^ differentiation
  -- degrees
  maxDegM     :: m -> Int                       -- ^ maximum degree
  totalDegM   :: m -> Int                       -- ^ total degree
  -- substitution and evaluation
  evalM       :: Num c => (VarM m -> c) -> m -> c                 -- ^ ring substitution (evaluation)
  varSubsM    :: (VarM m -> VarM m) -> m -> m                     -- ^ simple variable substitution
  termSubsM   :: Num c => (VarM m -> Maybe c) -> (m,c) -> (m,c)   -- ^ term substitution

{-
  -- some (inefficient) default implementations
  normalizeM     = id
  isNormalM      = const True
  productM       = foldl' mulM emptyM
  mulM a b       = productM [a,b]
  emptyM         = fromListM []
  variableM  v   = fromListM [(v,1)]
  singletonM v e = fromListM [(v,e)]
  maxDegM        = maximum      . map snd . toListM
  totalDegM      = foldl' (+) 0 . map snd . toListM
  isEmptyM       = null . toListM
-}

proxyVarM :: Monomial m => m -> Proxy (VarM m)
proxyVarM _ = Proxy

--------------------------------------------------------------------------------
-- * Polynomial rings

-- | The class of almost polynomial rings
class (Pretty p, Ring (CoeffP p), FreeModule p, CoeffP p ~ CoeffF p, MonomP p ~ BaseF p) => AlmostPolynomial p where

  -- | Type of coefficients
  type CoeffP p :: *
  -- | Type of monomials
  type MonomP p :: *
  -- | Type of variables
  type VarP   p :: *

  -- conversion
  fromListP     :: [(MonomP p, CoeffP p)] -> p       -- ^ construction from @(variable,exponent)@ pairs
  toListP       :: p -> [(MonomP p, CoeffP p)]       -- ^ extracting @(variable,exponent)@ pairs

  -- zero, one
  zeroP         :: p
  isZeroP       :: p -> Bool
  oneP          :: p

  -- construction
  variableP     :: VarP p        -> p                -- ^ a single variable
  singletonP    :: VarP p -> Int -> p                -- ^ a single variable raised to a power
  monomP        :: MonomP p -> p
  monomP'       :: MonomP p -> CoeffP p -> p
  scalarP       :: CoeffP p -> p

  -- algebra
  addP          :: p -> p -> p
  subP          :: p -> p -> p
  negP          :: p -> p 
  sumP          :: [p] -> p

  mulP          :: p -> p -> p
  productP      :: [p] -> p

  coeffOfP      :: MonomP p -> p -> CoeffP p
  mulByMonomP   :: MonomP p -> p -> p
  scaleP        :: CoeffP p -> p -> p 

  -- default implementations
  sumP     ps = case ps of { [] -> zeroP ; _ -> foldl1' addP ps }
  productP ps = case ps of { [] -> oneP  ; _ -> foldl1' mulP ps }

--------------------------------------------------------------------------------

-- | The class of polynomial rings
class (AlmostPolynomial p, Num p, Monomial (MonomP p), VarM (MonomP p) ~ VarP p) => Polynomial p where

  evalP         :: Num d => (CoeffP p -> d) -> (VarP p -> d) -> p -> d
  varSubsP      :: (VarP p -> VarP p) -> p -> p
  coeffSubsP    :: (VarP p -> Maybe (CoeffP p)) -> p -> p
  subsP         :: (VarP p -> p) -> p -> p

--------------------------------------------------------------------------------

proxyCoeffP :: AlmostPolynomial p => p -> Proxy (CoeffP p)
proxyCoeffP _ = Proxy

proxyMonomP :: AlmostPolynomial p => p -> Proxy (MonomP p)
proxyMonomP _ = Proxy

proxyVarP :: AlmostPolynomial p => p -> Proxy (VarP p)
proxyVarP _ = Proxy

--------------------------------------------------------------------------------
