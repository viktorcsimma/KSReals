-- Scientific notation with powers of 10.
-- Dyadics will be converted into this
-- to be printed more easily.
{-# OPTIONS --erasure #-}

module Implementation.Decimal where

{-# FOREIGN AGDA2HS {-# LANGUAGE MultiParamTypeClasses #-} #-}

open import Tool.Cheat

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_+_; _-_; _*_; _<_)
open import Agda.Builtin.Int
open import Haskell.Prim.Show
open import Haskell.Prim.Tuple
open import Haskell.Prim using (if_then_else_)

open import Tool.ErasureProduct
open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Order
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Implementation.Dyadic
open import Operator.Abs
open import Operator.Cast
open import Operator.Decidable
open import Operator.Pow
open import Operator.ShiftL
open import Operator.Shift
open import Operator.ExactShift

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Bool, Integer, fst, snd, (.), (==), until, otherwise, fromIntegral)
import Numeric.Natural

import Algebra.Ring
import Implementation.Nat
import Implementation.Int
import Implementation.Rational
import Operator.Abs
import Operator.Cast
import Operator.Pow
import Operator.ShiftL
import Operator.Shift
import Operator.ExactShift
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
halveDec x = if (intRem (decMant x) (pos 2) tt ≃# pos 0)
             then MkDec (shift (decMant x) (negsuc 0)) (decExpo x)
             else MkDec (pos 5 * decMant x) (decExpo x - pos 1)
{-# FOREIGN AGDA2HS
halveDec :: Decimal -> Decimal
halveDec (MkDec m e)
  | Prelude.even m      = MkDec (m `Prelude.div` 2) e
  | otherwise           = MkDec (5 * m) (e Prelude.- 1)
#-}

-- Actually, we should somehow generalise dyadics and decimals
-- into one category
-- to avoid code duplication.

-- Bringing two decimals to the same exponent
-- while retaining the values.
-- This will be needed for deciding order.
private
  compare : (Int -> Int -> Bool) -> Decimal -> Decimal -> Bool
  compare _##_ (MkDec m1 e1) (MkDec m2 e2) with (e1 <# e2)
  ... | true = m1 ## (m2 * pos 10 ^ natAbs (e2 - e1))
  ... | false = (m1 * pos 10 ^ natAbs (e1 - e2)) ## m2
  {-# FOREIGN AGDA2HS
  compare :: (Int -> Int -> Bool) -> Decimal -> Decimal -> Bool
  compare f (MkDec m1 e1) (MkDec m2 e2)
    = if e1 <# e2
      then f m1 (shift m2 (e2 - e1))
      else f (shift m1 (e1 - e2)) m2
  #-}

  decEq decLe decLt : Decimal -> Decimal -> Bool
  decEq = compare _≃#_
  decLe = compare _≤#_
  decLt = compare _<#_
  {-# COMPILE AGDA2HS decEq #-}
  {-# COMPILE AGDA2HS decLe #-}
  {-# COMPILE AGDA2HS decLt #-}

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

  ringDecimal : Ring Decimal
  Ring.super ringDecimal = semiRingDecimal
  Ring.negate ringDecimal (MkDec m e) = MkDec (negate m) e
  Ring.+-inverseˡ ringDecimal = cheat
  Ring.+-inverseʳ ringDecimal = cheat
  {-# COMPILE AGDA2HS ringDecimal #-}

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

  castDecimalRational : Cast Decimal Rational
  Cast.cast castDecimalRational (MkDec m (pos n)) = MkFrac (m * (pos 10) ^ n) (pos 1) tt
  Cast.cast castDecimalRational (MkDec m (negsuc n)) = MkFrac m ((pos 10) ^ (suc n)) cheat
  {-# FOREIGN AGDA2HS
  instance Cast Decimal Rational where
    cast (MkDec m e) = if 0 ≤# e then MkFrac (m * (10 ^ natAbs e)) 1
                                 else MkFrac m (pos 10 ^ natAbs e)
  #-}

  strongSetoidDecimal : StrongSetoid Decimal
  StrongSetoid.super strongSetoidDecimal = setoidDecimal
  StrongSetoid._><_ strongSetoidDecimal x y = cast {Decimal} {Rational} x >< cast {Decimal} {Rational} y
  StrongSetoid.><-irrefl strongSetoidDecimal {x = x} {y = y} = cheat
  StrongSetoid.><-sym strongSetoidDecimal {x = x} {y = y} = ><-sym {x = cast {Decimal} {Rational} x} {y = cast {Decimal} {Rational} y}
  StrongSetoid.><-cotrans strongSetoidDecimal {x = x} {y = y} neq z = ><-cotrans {x = cast {Decimal} {Rational} x} {y = cast {Decimal} {Rational} y} neq (cast {Decimal} {Rational} z)
  StrongSetoid.><-tight-apart strongSetoidDecimal {x = x} {y = y} = cheat
  {-# COMPILE AGDA2HS strongSetoidDecimal #-}

  leDecimal : Le Decimal
  Le._≤_ leDecimal x y = cast {Decimal} {Rational} x ≤ cast {Decimal} {Rational} y
  {-# COMPILE AGDA2HS leDecimal #-}

  decLeDecimal : DecLe Decimal
  DecLe.le decLeDecimal = leDecimal
  DecLe._≤#_ decLeDecimal = decLe
  DecLe.≤#-correct decLeDecimal x y = cheat
  {-# COMPILE AGDA2HS decLeDecimal #-}

  partialOrderDecimal : PartialOrder Decimal
  PartialOrder.le partialOrderDecimal = leDecimal
  PartialOrder.setoid partialOrderDecimal = setoidDecimal
  PartialOrder.≤-proper partialOrderDecimal x x' y y' eqx eqy = cheat
  {-# COMPILE AGDA2HS partialOrderDecimal #-}

  ltDecimal : Lt Decimal
  Lt._<_ ltDecimal x y = cast {Decimal} {Rational} x < cast {Decimal} {Rational} y
  {-# COMPILE AGDA2HS ltDecimal #-}

  decLtDecimal : DecLt Decimal
  DecLt.lt decLtDecimal = ltDecimal
  DecLt._<#_ decLtDecimal = decLt
  DecLt.<#-correct decLtDecimal x y = cheat
  {-# COMPILE AGDA2HS decLtDecimal #-}
  
  pseudoOrderDecimal : PseudoOrder Decimal
  PseudoOrder.strongSetoid pseudoOrderDecimal = strongSetoidDecimal
  PseudoOrder.lt pseudoOrderDecimal = ltDecimal
  PseudoOrder.<-asym pseudoOrderDecimal {x} {y} = <-asym {x = cast {Decimal} {Rational} x} {y = cast {Decimal} {Rational} y}
  PseudoOrder.<-cotrans pseudoOrderDecimal {x} {y} neq z = <-cotrans {x = cast {Decimal} {Rational} x} {y = cast {Decimal} {Rational} y} neq (cast {Decimal} {Rational} z)
  PseudoOrder.<-total pseudoOrderDecimal x y = <-total (cast {Decimal} {Rational} x) (cast {Decimal} {Rational} y)
  {-# COMPILE AGDA2HS pseudoOrderDecimal #-}

  absDecimal : Abs Decimal
  Abs.ring absDecimal = ringDecimal
  Abs.le absDecimal = leDecimal
  Abs.abs absDecimal x = MkDec (abs (decMant x)) (decExpo x)
  Abs.absCorrect absDecimal x = cheat
  {-# COMPILE AGDA2HS absDecimal #-}

@0 halveDecCorrect : ∀ (x : Decimal) -> (one + one) * halveDec x ≃ x
halveDecCorrect x = cheat

-- This rounds a rational to a decimal with the given precision of decimal digits (after the decimal point).
-- We first write it on positive rationals so that we don't have to bother with signs.
posRationalToDecimal : (x : PosRational) (prec : Nat) -> Decimal
posRationalToDecimal (MkFrac num₁ den₁ denNotNull₁ :&: qpos) prec
    = go (natDiv (natAbs num₁) (natAbs den₁) cheat) 0
         (natMod (natAbs num₁) (natAbs den₁) cheat) (natAbs den₁) cheat
         prec
  where
  -- the exponent will actually be negative
  go : (dMant dNegExpo remNum remDen : Nat) (@0 remDenNotNull : remDen ≢0) (prec : Nat) -> Decimal
  go dMant dNegExpo zero remDen remDenNotNull prec = MkDec (pos dMant) (negate (pos dNegExpo))
  go dMant dNegExpo (suc remNumm1) remDen remDenNotNull zero = let remNum = suc remNumm1 in
    -- checking the next digit for correct rounding
    if natDiv (10 * remNum) remDen remDenNotNull <# 5
    then MkDec (pos dMant) (negate (pos dNegExpo))
    else MkDec (pos (suc dMant)) (negate (pos dNegExpo))
  go dMant dNegExpo (suc remNumm1) remDen remDenNotNull (suc precm1)
    = let remNum = suc remNumm1; tenRemNum = 10 * remNum in
      go (10 * dMant + natDiv tenRemNum remDen remDenNotNull) (suc dNegExpo)
         (natMod tenRemNum remDen remDenNotNull) remDen remDenNotNull
         precm1
{-# FOREIGN AGDA2HS
posRationalToDecimal :: PosRational -> Natural -> Decimal
posRationalToDecimal ((:&:) (MkFrac num₁ den₁)) prec
    = go (natDiv (natAbs num₁) (natAbs den₁)) 0
         (natMod (natAbs num₁) (natAbs den₁)) (natAbs den₁)
         prec
  where
  -- the exponent will actually be negative
  go :: Natural -> Natural -> Natural -> Natural -> Natural -> Decimal
  go dMant dNegExpo 0 remDen prec = MkDec (pos dMant) (negate (pos dNegExpo))
  go dMant dNegExpo remNum remDen 0 =
    -- checking the next digit for correct rounding
    if natDiv (10 * remNum) remDen <# 5
    then MkDec (pos dMant) (negate (pos dNegExpo))
    else MkDec (pos (1 + dMant)) (negate (pos dNegExpo))
  go dMant dNegExpo remNum remDen prec
    = let tenRemNum = 10 * remNum in
      go (10 * dMant + natDiv tenRemNum remDen) (1 + dNegExpo)
         (natMod tenRemNum remDen) remDen
         (prec Prelude.- 1)
#-}

rationalToDecimal : (x : Rational) (prec : Nat) -> Decimal
rationalToDecimal x prec = if null ≤# x then posRationalToDecimal (x :&: cheat) prec
                                        else negate (posRationalToDecimal (abs x :&: cheat) prec)
{-# COMPILE AGDA2HS rationalToDecimal #-}

-- With dyadics, it's actually easier to compute the exact decimal value
-- and then round it.
dyadicToExactDecimal : Dyadic -> Decimal
dyadicToExactDecimal x = shift (MkDec (mant x) (pos 0)) (expo x)
{-# COMPILE AGDA2HS dyadicToExactDecimal #-}

@0 dyadicToExactDecimalCorrect : ∀ (x : Dyadic) -> dToQSlow x ≃ decToQSlow (dyadicToExactDecimal x)
dyadicToExactDecimalCorrect = cheat

-- Negative precision is when some of the digits before the decimal point are also 0.
-- But the exponent has the opposite sign.
{-# TERMINATING #-}
roundNonNegDecimal : (x : Decimal) (@0 nonNegx : null ≤ x)  (prec : Int) -> Decimal
roundNonNegDecimal x nonNegx prec =
  if pos 0 ≤# precDiff then x    -- then, we would win nothing by shifting the mantissa upwards
                       else (if snd goResult <# 5
                             then goDec
                             else MkDec (pos 1 + decMant goDec) (decExpo goDec))
  where
  precDiff : Int
  precDiff = decExpo x + prec
  -- also returns the last digit
  go : (x : Decimal) (previousDigit steps : Nat) -> Decimal × Nat
  -- let's rather write this in a compilable way
  go (MkDec m e) prevD steps =
    if steps ≃# 0 then (MkDec m e , prevD) else
    go (MkDec (intQuot m (pos 10) tt)
              (pos 1 + e))
       (natMod (natAbs m) 10 tt)
       (natAbs (negsuc 0 + pos steps))
  goResult : Decimal × Nat
  goResult = go x 0 (natAbs precDiff)
  goDec : Decimal
  goDec = fst goResult
{-# COMPILE AGDA2HS roundNonNegDecimal #-}

roundDecimal : (x : Decimal) (prec : Int) -> Decimal
roundDecimal x prec = if null ≤# x then roundNonNegDecimal x cheat prec
                                   else negate (roundNonNegDecimal (negate x) cheat prec)
{-# COMPILE AGDA2HS roundDecimal #-}

dyadicToDecimal : (x : Dyadic) (prec : Nat) -> Decimal
dyadicToDecimal x prec = roundDecimal (dyadicToExactDecimal x) (pos prec)
{-# COMPILE AGDA2HS dyadicToDecimal #-}
