-- Show instances for different types
-- (mainly for Dyadics, as they will be primarily used).
module Tools.Show where

{-# FOREIGN AGDA2HS
import Implementations.Rational
import Implementations.Dyadic
#-}

open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List
open import Haskell.Prim.String
open import Haskell.Prim.List
open import Haskell.Prim.Show
open import Haskell.Prim.Tuple
open import Haskell.Prim using (const; if_then_else_)

open import Algebra.Ring
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Dyadic
open import Implementations.Rational
open import Operations.ShiftL
open import Operations.Pow

-- We have to define this separately
-- for the sake of the termination checker.
showDyadic : Dyadic -> String
showDyadic (m :|^ pos zero) = show m
showDyadic (m :|^ pos n) = show (m * shiftl one (pos n))
showDyadic (m :|^ negsuc n) = sign m ++ showWithDecimalPoint
                                                    (go (natAbs m) zero (suc n) zero)
  where
  sign : Int -> String
  sign (pos _)    = []
  sign (negsuc _) = '-' ∷ []

  -- With every right shift, we multiply
  -- the number to the right by 5 and
  -- add 5000.. to it if we had a remainder of 1
  -- at the left.
  go : (left right : Nat) (stepsLeft : Nat) (stepsDone : Nat) -> Nat × Nat
  go left right zero    _ = (left , right)
  go left right (suc n) m = go (natDiv left 2)
                               (5 * right
                                  + (if (natMod left 2 == 1) then (5 * 10 ^ m) else 0))
                               n (suc m)
                               -- TODO : cut down the last zeroes;
                               -- they don't represent a decimal precision
  showWithDecimalPoint : Nat × Nat -> String
  showWithDecimalPoint (left , right) = show left ++ '.' ∷ show right
-- Again, there are some dirty pattern matchings here; so...
{-# FOREIGN AGDA2HS
showDyadic :: Dyadic -> String
showDyadic (m :|^ 0) = show m
showDyadic (m :|^ n)
  | n > 0     = show (m * 2 ^ n)
  | otherwise = sign m ++ showWithDecimalPoint
                                     (go (abs m) 0 (abs n) 0)
  where
  sign :: Integer -> String
  sign x = if (0 > x) then "-" else ""

  go :: Integer -> Integer -> Integer -> Integer -> (Integer, Integer)
  go left right 0    _ = (left , right)
  go left right sucn m = go (quot left 2)
                               (5 * right
                                  + (if (rem left 2 == 1) then (5 * 10 ^ m) else 0))
                               (sucn - 1) (m + 1)
                               -- TODO : cut down the last zeroes;
                               -- they don't represent a decimal precision
  showWithDecimalPoint :: (Integer, Integer) -> String
  showWithDecimalPoint (left, right) = show left ++ '.' : show right
#-}

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
