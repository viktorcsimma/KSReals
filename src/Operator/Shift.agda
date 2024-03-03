-- A type class for types
-- which have a shift operation
-- (that is, shifting with an integer
-- which might also be negative).
{-# OPTIONS --erasure #-}

module Operator.Shift where

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_+_; _*_)
open import Agda.Builtin.Int
open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Operator.Pow
open import Implementation.Nat
open import Implementation.Int

open import Operator.ShiftL

{-# FOREIGN AGDA2HS
-- for the builtin shift:
import qualified Data.Bits (shift)

import Implementation.Nat
import Implementation.Int
import Algebra.SemiRing hiding ((*))
import Operator.ShiftL
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

