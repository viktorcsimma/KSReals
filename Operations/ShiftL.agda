-- A type class for types
-- which have a shift operation.
{-# OPTIONS --erasure #-}

module Operations.ShiftL where

open import Tools.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_+_; _*_)
open import Agda.Builtin.Int
open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.Ring
open import Operations.Pow
open import Implementations.Nat
open import Implementations.Int

{-# FOREIGN AGDA2HS
-- for the builtin shift:
import qualified Data.Bits (shift)

import Implementations.Nat
import Implementations.Int
import Algebra.Ring hiding ((*))
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

record Shift (a : Set) : Set₁ where
  field
    overlap {{super}} : ShiftL a
    shift : a -> Int -> a
    @0 shiftProper : ∀ (x x' : a) (y y' : Int)
                           -> x ≃ x' -> y ≃ y' -> shift x y ≃ shift x' y'
    @0 shiftEquivalent : ∀ (x : a) (n : Nat) -> shiftl x n ≃ shift x (pos n)
    @0 shiftLeftThenRight : ∀ (x : a) (n : Nat) -> shift (shift x (pos n)) (negate (pos n)) ≃ x
    -- The other way round, it might not be true because of rounding
    -- (there will be a separate class where we require that).
open Shift {{...}} public
{-# COMPILE AGDA2HS Shift class #-}


-- We need an integer shift operation, too.
-- Of course, if the integer is negative, we will have to round.
-- E.g. 4.5 will be rounded to 4; -0.5 to -1.
private
  intShiftf : Int -> Int -> Int
  intShiftf x (pos n) = shiftl x n
  intShiftf x (negsuc zero) = halveInt x
  intShiftf x (negsuc (suc n)) = intShiftf (halveInt x) (negsuc n)
  -- I won't handle x ≡ pos zero separately (we'll use a Haskell function in runtime anyway).

instance
  intShift : Shift Int
  Shift.super intShift = intShiftL
  Shift.shift intShift = intShiftf
  Shift.shiftProper intShift _ _ _ _ refl refl = refl
  Shift.shiftEquivalent intShift x zero = refl
  Shift.shiftEquivalent intShift x (suc n) = refl
  Shift.shiftLeftThenRight intShift x n = cheat
  {-# FOREIGN AGDA2HS
  -- We also use Data.Bits.shift here.
  instance Shift Integer where
    shift x n = Data.Bits.shift x (Prelude.fromIntegral n)
  #-}

-- And now a separate class for when
-- shifting to the right is exact and does not come with loss of precision
-- (used for the rationals and dyadics).
record ExactShift (a : Set) : Set₁ where
  field
    overlap {{super}} : Shift a
    @0 shiftRightThenLeft : ∀ (x : a) (n : Nat) -> shift (shift x (negate (pos n))) (pos n) ≃ x
open ExactShift {{...}} public
{-# COMPILE AGDA2HS ExactShift class #-}
