
{-# LANGUAGE FlexibleInstances #-}

-- | Pretty-printing.
--
-- Tip: you can try putting something like this into your @.ghci@ file to
-- make life more convenient:
--
-- > :m    +Math.Algebra.Polynomial.Pretty  
-- > :seti -interactive-print=prettyPrint
--
 
module Math.Algebra.Polynomial.Pretty where

--------------------------------------------------------------------------------

import Data.List
import Data.Ratio

import Math.Algebra.Polynomial.FreeModule ( FreeMod, ZMod, QMod )
import qualified Math.Algebra.Polynomial.FreeModule as ZMod

import Math.Algebra.Polynomial.Misc

--------------------------------------------------------------------------------

class Pretty a where
  pretty :: a -> String

  prettyInParens :: a -> String
  prettyInParens = pretty

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = putStrLn . pretty

--------------------------------------------------------------------------------

-- instance Pretty a => Pretty (ZMod a) where
--   pretty = prettyZMod pretty

instance (Num c, Eq c, Pretty c, IsSigned c, Pretty b) => Pretty (FreeMod c b) where
  pretty = prettyFreeMod' True pretty
  prettyInParens x = "(" ++ pretty x ++ ")"

--------------------------------------------------------------------------------

instance Pretty Integer where
  pretty = show

instance (Eq a, Num a, Pretty a) => Pretty (Ratio a) where
  pretty q = case denominator q of
    1 -> prettyInParens (numerator q)
    _ -> prettyInParens (numerator q) ++ "/" ++ prettyInParens (denominator q)

--------------------------------------------------------------------------------
-- * Pretty printing elements of free modules

-- | Example: @showVarPower "x" 5 == "x^5"@
showVarPower :: String -> Int -> String
showVarPower name expo = case expo of
  0 -> "1"
  1 -> name
  _ -> name ++ "^" ++ show expo

--------------------------------------------------------------------------------

-- | no multiplication sign (ok for mathematica and humans)
prettyZMod_ :: (b -> String) -> ZMod b -> String
prettyZMod_ = prettyFreeMod' False
  
-- | multiplication sign (ok for maple etc)
prettyZMod :: (b -> String) -> ZMod b -> String
prettyZMod = prettyFreeMod' True

--------------------------------------------------------------------------------

prettyFreeMod' 
  :: (Num c, Eq c, IsSigned c, Pretty c) 
  => Bool                -- ^ use star for multiplication (@False@ means just concatenation)
  -> (b -> String)       -- ^ show base
  -> FreeMod c b 
  -> String
prettyFreeMod' star showBase what = final where
  final = if take 3 stuff == " + " then drop 3 stuff else drop 1 stuff
  stuff = concatMap f (ZMod.toList what) 
  f (g,  1) = plus  ++ showBase' g
  f (g, -1) = minus ++ showBase' g
  f (g, c)  = case showBase' g of
    "1" -> sgn c ++ (prettyInParens $ abs c)
    b   -> sgn c ++ (prettyInParens $ abs c) ++ starStr ++ b
  -- cond (_,c) = (c/=0)
  starStr = if star then "*" else " "
  showBase' g = case showBase g of
    "" -> "1"  -- "(1)"
    s  -> s
  sgn c = case signOf c of
    Just Minus -> minus
    _          -> plus
  plus  = " + "
  minus = " - "

prettyFreeMod'' 
  :: (c -> String)    -- ^ show coefficient
  -> (b -> String)    -- ^ show base
  -> FreeMod c b 
  -> String
prettyFreeMod'' showCoeff showBase what = result where
  result = intercalate " + " (map f $ ZMod.toList what) 
  f (g, c) = case showBase g of
    ""  -> showCoeff c
    "1" -> showCoeff c
    b   -> showCoeff c ++ starStr ++ b
  starStr = "*"

--------------------------------------------------------------------------------

{-
-- * Utility

-- | Put into parentheses
paren :: String -> String
paren s = '(' : s ++ ")"

--------------------------------------------------------------------------------

{-

-- | Exponential form of a partition
expFormString :: Partition -> String
expFormString p = "(" ++ intercalate "," (map f ies) ++ ")" where
  ies = toExponentialForm p
  f (i,e) = show i ++ "^" ++ show e
-}

extendStringL :: Int -> String -> String
extendStringL k s = s ++ replicate (k - length s) ' '

extendStringR :: Int -> String -> String
extendStringR k s = replicate (k - length s) ' ' ++ s

--------------------------------------------------------------------------------
-- * Mathematica-formatted output

class Mathematica a where
  mathematica :: a -> String

instance Mathematica Int where
  mathematica = show

instance Mathematica Integer where
  mathematica = show

instance Mathematica String where
  mathematica = show

{-
instance Mathematica Partition where
  mathematica (Partition ps) = "{" ++ intercalate "," (map show ps) ++ "}"
-}

data Indexed a = Indexed String a

instance Mathematica a => Mathematica (Indexed a) where
  mathematica (Indexed x sub) = "Subscript[" ++ x ++ "," ++ mathematica sub ++ "]"

--------------------------------------------------------------------------------

-}
