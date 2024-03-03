-- A type class for types
-- which have a shiftL operation
-- (that is, shifting with a natural).
{-# OPTIONS --erasure #-}

module Operator.ShiftL where

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_+_; _*_)
open import Agda.Builtin.Int
open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.SemiRing
open import Operator.Pow
open import Implementation.Nat
open import Implementation.Int

{-# FOREIGN AGDA2HS
-- for the builtin shift:
import qualified Data.Bits (shift)

import Implementation.Nat
import Implementation.Int
import Algebra.SemiRing hiding ((*))
#-}

-- Now we take a less general, but more practical approach:
-- we fix that the second type must either be Nat or Int.

record ShiftL (a : Set) : Set₁ where
  field
    overlap {{semiringa}} : SemiRing a
    shiftl : a -> Nat -> a
    @0 shiftlProper : ∀ (x x' : a) (y y' : Nat)
                           -> x ≃ x' -> y ≃ y' -> shiftl x y ≃ shiftl x' y'
    @0 shiftlNull : ∀ (x : a) -> shiftl x zero ≃ x
    @0 shiftlSuc : ∀ (x : a) (y : Nat) -> shiftl x (suc y) ≃ shiftl ((one + one) * x) y
open ShiftL {{...}} public
{-# COMPILE AGDA2HS ShiftL class #-}

-- Records do not like recursive function definitions; so:
private
  shiftNat : Nat -> Nat -> Nat
  shiftNat n zero = n
  shiftNat n (suc k) = 2 * shiftNat n k

instance
  shiftLNat : ShiftL Nat
  ShiftL.semiringa shiftLNat = semiRingNat
  ShiftL.shiftl shiftLNat = shiftNat
  ShiftL.shiftlProper shiftLNat _ _ _ _ refl refl = refl
  ShiftL.shiftlNull shiftLNat _ = refl
  ShiftL.shiftlSuc shiftLNat x y = cheat
  -- {-# COMPILE AGDA2HS shiftLNat #-}
  -- For there is a `suc` constructor:
  {-# FOREIGN AGDA2HS
  instance ShiftL Nat where
    shiftl n 0 = n
    shiftl n k = 2 * shiftl n (k Prelude.- 1)
  #-}

  intShiftL : ShiftL Int
  ShiftL.semiringa intShiftL = semiRingInt
  ShiftL.shiftl intShiftL x k = x * (pos 2) ^ k
  ShiftL.shiftlProper intShiftL _ _ _ _ refl refl = refl
  ShiftL.shiftlNull intShiftL x = *-identityʳ x
  ShiftL.shiftlSuc intShiftL x y = cheat
  {-# FOREIGN AGDA2HS
  -- Actually, there is a builtin shift function in Data.Bits.
  instance ShiftL Integer where
    shiftl x k = Data.Bits.shift x (Prelude.fromIntegral k)
  #-}
