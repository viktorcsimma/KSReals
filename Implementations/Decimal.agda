-- Scientific notation with powers of 10.
-- Dyadics will be converted into this
-- to be printed more easily.
{-# OPTIONS --erasure #-}

module Implementations.Decimal where

open import Tools.Cheat

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_+_; _-_; _*_)
open import Agda.Builtin.Int
open import Haskell.Prim.Show
open import Haskell.Prim using (if_then_else_)

open import Algebra.Setoid
open import Algebra.Ring
open import Implementations.Dyadic
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
open import Operations.Decidable
open import Operations.Pow
open import Operations.ShiftL

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, fst, snd, (.), (==), until, otherwise, fromIntegral)
import Numeric.Natural

import Implementations.Int
import Operations.Abs
import Operations.Pow
import Operations.ShiftL
#-}

-- This can be interpreted as mant * 10 ^ expo.
record Decimal : Set where
  constructor MkDec
  field
    decMant decExpo : Int
open Decimal public
{-# COMPILE AGDA2HS Decimal #-}

-- This part goes similarly to Dyadic.

tenPowInt : Int -> Rational
tenPowInt (pos n) = MkFrac (pos 10 ^ n) one tt
tenPowInt (negsuc n) = MkFrac one (pos 10 ^ (suc n)) cheat
{-# FOREIGN AGDA2HS
tenPowInt :: Integer -> Rational
tenPowInt n
  | 0 ≤# n      = MkFrac (10 ^ (fromIntegral n :: Natural)) 1
  | otherwise   = MkFrac 1 (10 ^ (fromIntegral (abs n) :: Natural))
#-}

decToQSlow : Decimal -> Rational
decToQSlow d = MkFrac (decMant d) (pos 1) tt * tenPowInt (decExpo d)
{-# COMPILE AGDA2HS decToQSlow #-}

-- If the mantissa is even, we simply divide it by 2;
-- otherwise, we multiply it by 5 and decrement the exponent
-- (that means *5/10).
halveDec : Decimal -> Decimal
halveDec x = if (intRem (decMant x) (pos 2) ≃# pos 0)
             then MkDec (shift (decMant x) (negsuc 0)) (decExpo x)
             else MkDec (pos 5 * decMant x) (decExpo x - pos 1)
{-# FOREIGN AGDA2HS
halveDec :: Decimal -> Decimal
halveDec (MkDec m e)
  | Prelude.even m      = MkDec (m `Prelude.div` 2) e
  | otherwise           = MkDec (5 * m) (e Prelude.- 1)
#-}

instance
  -- We define equality by converting both sides to rationals.
  setoidDecimal : Setoid Decimal
  Setoid._≃_ setoidDecimal x y = decToQSlow x ≃ decToQSlow y
  Setoid.≃-refl setoidDecimal {x} = ≃-refl {x = num (decToQSlow x) * den (decToQSlow x)}
  Setoid.≃-sym setoidDecimal {x} {y} = ≃-sym {x = decToQSlow x} {y = decToQSlow y}
  Setoid.≃-trans setoidDecimal {x} {y} {z} = ≃-trans {x = decToQSlow x} {y = decToQSlow y} {z = decToQSlow z}
  {-# COMPILE AGDA2HS setoidDecimal #-}

  semiRingDecimal : SemiRing Decimal
  SemiRing.super semiRingDecimal = setoidDecimal
  -- Uh... what about an absolute value? Can that be used somehow?
  (semiRingDecimal SemiRing.+  (MkDec decMantx decExpox)) (MkDec decManty decExpoy) =
    if decExpox ≤# decExpoy
      then MkDec (decMantx + shift decManty (decExpoy + negate decExpox))
                   decExpox
      else MkDec (shift decMantx (decExpox + negate decExpoy) + decManty)
                   decExpoy
  (semiRingDecimal SemiRing.* (MkDec decMantx decExpox)) (MkDec decManty decExpoy)
                   = MkDec (decMantx * decManty) (decExpox + decExpoy)
  -- Uh; these are going to be pretty hard to work with.
  SemiRing.+-proper semiRingDecimal eq = cheat
  SemiRing.+-assoc semiRingDecimal = cheat
  SemiRing.*-proper semiRingDecimal = cheat
  SemiRing.*-assoc semiRingDecimal = cheat
  SemiRing.null semiRingDecimal = MkDec null null
  SemiRing.one semiRingDecimal = MkDec one null
  SemiRing.NonZero semiRingDecimal x = NonZero (decMant x)
  SemiRing.NonZeroCorrect semiRingDecimal x = cheat
  SemiRing.NonZeroOne semiRingDecimal = tt
  SemiRing.+-identityˡ semiRingDecimal = cheat
  SemiRing.+-identityʳ semiRingDecimal = cheat
  SemiRing.*-identityˡ semiRingDecimal x = cheat
  SemiRing.*-identityʳ semiRingDecimal = cheat
  SemiRing.+-comm semiRingDecimal = cheat
  SemiRing.*-comm semiRingDecimal = cheat
  SemiRing.*-nullˡ semiRingDecimal = cheat
  SemiRing.*-nullʳ semiRingDecimal = cheat
  SemiRing.*-distribˡ-+ semiRingDecimal = cheat
  SemiRing.*-distribʳ-+ semiRingDecimal = cheat
  {-# COMPILE AGDA2HS semiRingDecimal #-}

  shiftLDecimal : ShiftL Decimal
  ShiftL.semiringa shiftLDecimal = semiRingDecimal
  ShiftL.shiftl shiftLDecimal x n = MkDec (shiftl (pos 1) n * decMant x) (decExpo x)
  ShiftL.shiftlProper shiftLDecimal = cheat
  ShiftL.shiftlNull shiftLDecimal = cheat
  ShiftL.shiftlSuc shiftLDecimal = cheat
  {-# COMPILE AGDA2HS shiftLDecimal #-}

  shiftDecimal : Shift Decimal
  Shift.super shiftDecimal = shiftLDecimal
  Shift.shift shiftDecimal x (pos n) = shiftl x n
  Shift.shift shiftDecimal x (negsuc zero) = halveDec x
  Shift.shift shiftDecimal x (negsuc (suc n)) = shift (halveDec x) (negsuc n)
  Shift.shiftProper shiftDecimal = cheat
  Shift.shiftEquivalent shiftDecimal = cheat
  Shift.shiftLeftThenRight shiftDecimal = cheat
  {-# FOREIGN AGDA2HS
  instance Shift Decimal where
    shift x n
      | 0 ≤# n     = shiftl x (fromIntegral n)
      | otherwise  = snd (until ((==0) . fst) (\ (k, d) -> (k+1, halveDec d)) (n, x))
  #-}

  exactShiftDecimal : ExactShift Decimal
  ExactShift.super exactShiftDecimal = shiftDecimal
  ExactShift.shiftRightThenLeft exactShiftDecimal = cheat
  {-# COMPILE AGDA2HS exactShiftDecimal #-}

@0 halveDecCorrect : ∀ (x : Decimal) -> (one + one) * halveDec x ≃ x
halveDecCorrect x = cheat

-- This will be called first when printing a Dyadic.
dyadicToDecimal : Dyadic -> Decimal
dyadicToDecimal x = shift (MkDec (mant x) (pos 0)) (expo x)
{-# COMPILE AGDA2HS dyadicToDecimal #-}

@0 dyadicToDecimalCorrect : ∀ (x : Dyadic) -> dToQSlow x ≃ decToQSlow (dyadicToDecimal x)
dyadicToDecimalCorrect = cheat
