-- Show instances for different types
-- (mainly for Dyadics, as they will be primarily used).
{-# OPTIONS --erasure #-}

module Tools.Show where

{-# FOREIGN AGDA2HS
import Implementations.Rational
import Implementations.Dyadic
#-}

open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List
open import Haskell.Prelude using (reverse)
open import Haskell.Prim.String
open import Haskell.Prim.List
open import Haskell.Prim.Show
open import Haskell.Prim.Tuple
open import Haskell.Prim using (const; if_then_else_)

open import Algebra.Ring
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Decimal
open import Implementations.Dyadic
open import Implementations.Rational
open import Operations.ShiftL
open import Operations.Pow

{-# FOREIGN AGDA2HS
import Numeric.Natural

import Implementations.Decimal
#-}

-- Printing a Decimal.
-- It will be much easier than to print a Dyadic
-- because we only need to position the decimal point.
showDecimal : Decimal -> String
-- For performance reasons; if n is nonnegative, we don't reverse strings and such.
showDecimal (MkDec m (pos n)) = show (m * pos 10 ^ n)
showDecimal (MkDec m (negsuc n)) = go (suc n) (reverse (show m)) []
  where
  -- The two sides
  -- represent where we are;
  -- but the front of the list is the digit closest to us
  -- (for performance reasons).
  -- E.g. ("43210" , "56789") is "01234_56789".
  go : Nat -> String -> String -> String
  go zero [] [] = '0' ∷ []
  go zero [] right = '0' ∷ '.' ∷ right
  go zero left [] = reverse left
  go zero left right = reverse left ++ '.' ∷ right
  go (suc n) [] right = go n [] ('0' ∷ right)
  go (suc n) (x ∷ left) right = go n left (x ∷ right)
{-# FOREIGN AGDA2HS
showDecimal :: Decimal -> String
-- For performance reasons; if n is nonnegative, we don't reverse strings and such.
showDecimal (MkDec m n)
  | 0 <= n      = show (m * 10 ^ fromIntegral n)
  | otherwise   = go (fromIntegral (abs n)) (reverse (show m)) []
    where
    -- The two sides
    -- represent where we are;
    -- but the front of the list is the digit closest to us
    -- (for performance reasons).
    -- E.g. ("43210" , "56789") is "01234_56789".
    go :: Natural -> String -> String -> String
    go 0 [] [] = '0' : []
    go 0 [] right = '0' : '.' : right
    go 0 left [] = reverse left
    go 0 left right = reverse left ++ '.' : right
    go sucn [] right = go (sucn - 1) [] ('0' : right)
    go sucn (x : left) right = go (sucn - 1) left (x : right)
#-}

instance
  iShowDecimal : Show Decimal
  Show.show iShowDecimal = showDecimal
  Show.showsPrec iShowDecimal _ x s = showDecimal x ++ s
  Show.showList iShowDecimal = defaultShowList (const show)
  {-# FOREIGN AGDA2HS
  instance Show Decimal where
    show = showDecimal
  #-}

-- And we simply convert a Dyadic to a Decimal first.
showDyadic : Dyadic -> String
showDyadic x = showDecimal (dyadicToDecimal x)
{-# COMPILE AGDA2HS showDyadic #-}

instance
  iShowDyadic : Show Dyadic
  Show.show iShowDyadic = showDyadic
  Show.showsPrec iShowDyadic _ x s = showDyadic x ++ s
  Show.showList iShowDyadic = defaultShowList (const show)
  {-# FOREIGN AGDA2HS
  instance Show Dyadic where
    show = showDyadic
  #-}

  iShowFrac : {a : Set} {{semiring : SemiRing a}} {{showa : Show a}} -> Show (Frac a)
  Show.show iShowFrac q = show (num q) ++ ' ' ∷ '/' ∷ ' ' ∷ show (den q)
  Show.showsPrec iShowFrac _ x s = show x ++ s
  Show.showList iShowFrac = defaultShowList (const show)
  {-# FOREIGN AGDA2HS
  instance Show a => Show (Frac a) where
    show q = show (num q) ++ ' ' : '/' : ' ' : show (den q)
  #-}
