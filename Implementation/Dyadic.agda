-- A concrete implementation of dyadic numbers
-- and a proof that they are good for AppRational.
{-# OPTIONS --erasure #-}

module Implementation.Dyadic where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, Bool(..), id)

import Tool.ErasureProduct
import Operator.Decidable
import Operator.ShiftL
import Operator.Shift
import Operator.ExactShift
import Implementation.Int
import Implementation.Frac
import Implementation.Rational
import Algebra.SemiRing
import Algebra.Ring
#-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (id; if_then_else_; IsTrue; the)

open import Tool.Cheat

open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Operator.Abs
open import Operator.Cast
open import Operator.ShiftL
open import Operator.Shift
open import Operator.ExactShift
open import Operator.Pow
open import Operator.Decidable
open import Algebra.Order
open import Tool.ErasureProduct

-- For the sake of simplicity, we now use the concrete Int type.
-- It can be interpreted as mant * 2 ^ expo.
record Dyadic : Set where
  constructor _:|^_
  field
    mant expo : Int
open Dyadic public
infix 10 _:|^_
{-# COMPILE AGDA2HS Dyadic #-}

twoPowInt : Int -> Rational
twoPowInt n = shift (MkFrac (pos 1) (pos 1) tt) n
{-# COMPILE AGDA2HS twoPowInt #-}

dToQSlow : Dyadic -> Rational
dToQSlow d = MkFrac (mant d) (pos 1) tt * twoPowInt (expo d)
{-# COMPILE AGDA2HS dToQSlow #-}

-- Bringing two dyadics to the same exponent
-- while retaining the values.
-- This will be needed for deciding order.
private
  compare : (Int -> Int -> Bool) -> Dyadic -> Dyadic -> Bool
  compare _##_ (m1 :|^ e1) (m2 :|^ e2) with (e1 <# e2)
  ... | true = m1 ## shift m2 (e2 - e1)
  ... | false = shift m1 (e1 - e2) ## m2
  {-# FOREIGN AGDA2HS
  compare :: (Int -> Int -> Bool) -> Dyadic -> Dyadic -> Bool
  compare f (m1 :|^ e1) (m2 :|^ e2)
    = if e1 <# e2
      then f m1 (shift m2 (e2 - e1))
      else f (shift m1 (e1 - e2)) m2
  #-}

  dEq dLe dLt : Dyadic -> Dyadic -> Bool
  dEq = compare _≃#_
  dLe = compare _≤#_
  dLt = compare _<#_
  {-# COMPILE AGDA2HS dEq #-}
  {-# COMPILE AGDA2HS dLe #-}
  {-# COMPILE AGDA2HS dLt #-}

{-
@0 simplifyCorrect : ∀(d : Dyadic) -> simplify d ≃ d
simplifyCorrect = ?
-}

instance
  -- We define the Set equality by converting both sides to rationals.
  -- TODO: prove this is equivalent to the efficient version.
  setoidDyadic : Setoid Dyadic
  Setoid._≃_ setoidDyadic x y = dToQSlow x ≃ dToQSlow y
  Setoid.≃-refl setoidDyadic {x} = ≃-refl {x = num (dToQSlow x) * den (dToQSlow x)}
  Setoid.≃-sym setoidDyadic {x} {y} = ≃-sym {x = dToQSlow x} {y = dToQSlow y}
  Setoid.≃-trans setoidDyadic {x} {y} {z} = ≃-trans {x = dToQSlow x} {y = dToQSlow y} {z = dToQSlow z}
  {-# COMPILE AGDA2HS setoidDyadic #-}

  strongSetoidDyadic : StrongSetoid Dyadic
  StrongSetoid.super strongSetoidDyadic = setoidDyadic
  StrongSetoid._><_ strongSetoidDyadic x y = dToQSlow x >< dToQSlow y
  StrongSetoid.><-irrefl strongSetoidDyadic {x = x} {y = y} = ><-irrefl {x = dToQSlow x} {y = dToQSlow y}
  StrongSetoid.><-sym strongSetoidDyadic {x = x} {y = y} = ><-sym {x = dToQSlow x} {y = dToQSlow y}
  StrongSetoid.><-cotrans strongSetoidDyadic {x = x} {y = y} neq z = ><-cotrans {x = dToQSlow x} {y = dToQSlow y} neq (dToQSlow z)
  StrongSetoid.><-tight-apart strongSetoidDyadic {x = x} {y = y} = ><-tight-apart {x = dToQSlow x} {y = dToQSlow y}
  {-# COMPILE AGDA2HS strongSetoidDyadic #-}

  -- But this is the efficient one.
  decSetoidDyadic : DecSetoid Dyadic
  DecSetoid.setoid decSetoidDyadic = setoidDyadic
  DecSetoid._≃#_ decSetoidDyadic = dEq
  DecSetoid.≃#-correct decSetoidDyadic = cheat
  {-# COMPILE AGDA2HS decSetoidDyadic #-}

  semiRingDyadic : SemiRing Dyadic
  SemiRing.super semiRingDyadic = setoidDyadic
  -- Uh... what about an absolute value? Can that be used somehow?
  (semiRingDyadic SemiRing.+ mantx :|^ expox) (manty :|^ expoy) =
    if expox ≤# expoy
      then (mantx + shift manty (expoy + negate expox))
                   :|^ expox
      else (shift mantx (expox + negate expoy) + manty)
                   :|^ expoy
  (semiRingDyadic SemiRing.* mantx :|^ expox) (manty :|^ expoy)
                   = (mantx * manty) :|^ (expox + expoy)
  -- Uh; these are going to be pretty hard to work with.
  SemiRing.+-proper semiRingDyadic eq = cheat
  SemiRing.+-assoc semiRingDyadic = cheat
  SemiRing.*-proper semiRingDyadic = cheat
  SemiRing.*-assoc semiRingDyadic = cheat
  SemiRing.null semiRingDyadic = null :|^ null
  SemiRing.one semiRingDyadic = one :|^ null
  SemiRing.NonZero semiRingDyadic x = NonZero (mant x)
  SemiRing.NonZeroCorrect semiRingDyadic x = cheat
  SemiRing.NonZeroOne semiRingDyadic = tt
  SemiRing.+-identityˡ semiRingDyadic = cheat
  SemiRing.+-identityʳ semiRingDyadic = cheat
  SemiRing.*-identityˡ semiRingDyadic x = cheat
  SemiRing.*-identityʳ semiRingDyadic = cheat
  SemiRing.+-comm semiRingDyadic = cheat
  SemiRing.*-comm semiRingDyadic = cheat
  SemiRing.*-nullˡ semiRingDyadic = cheat
  SemiRing.*-nullʳ semiRingDyadic = cheat
  SemiRing.*-distribˡ-+ semiRingDyadic = cheat
  SemiRing.*-distribʳ-+ semiRingDyadic = cheat
  {-# COMPILE AGDA2HS semiRingDyadic #-}

  ringDyadic : Ring Dyadic
  Ring.super ringDyadic = semiRingDyadic
  Ring.negate ringDyadic (mantx :|^ expox) = negate mantx :|^ expox
  Ring.+-inverseˡ ringDyadic = cheat
  Ring.+-inverseʳ ringDyadic = cheat
  {-# COMPILE AGDA2HS ringDyadic #-}

  leDyadic : Le Dyadic
  Le._≤_ leDyadic x y = dToQSlow x ≤ dToQSlow y
  {-# COMPILE AGDA2HS leDyadic #-}

  decLeDyadic : DecLe Dyadic
  DecLe.le decLeDyadic = leDyadic
  DecLe._≤#_ decLeDyadic = dLe
  DecLe.≤#-correct decLeDyadic x y = cheat
  {-# COMPILE AGDA2HS decLeDyadic #-}

  partialOrderDyadic : PartialOrder Dyadic
  PartialOrder.le partialOrderDyadic = leDyadic
  PartialOrder.setoid partialOrderDyadic = setoidDyadic
  PartialOrder.≤-proper partialOrderDyadic x x' y y' eqx eqy = ≤-proper (dToQSlow x) (dToQSlow x') (dToQSlow y) (dToQSlow y') eqx eqy
  {-# COMPILE AGDA2HS partialOrderDyadic #-}

  ltDyadic : Lt Dyadic
  Lt._<_ ltDyadic x y = dToQSlow x < dToQSlow y
  {-# COMPILE AGDA2HS ltDyadic #-}

  decLtDyadic : DecLt Dyadic
  DecLt.lt decLtDyadic = ltDyadic
  DecLt._<#_ decLtDyadic = dLt
  DecLt.<#-correct decLtDyadic x y = cheat
  {-# COMPILE AGDA2HS decLtDyadic #-}
  
  pseudoOrderDyadic : PseudoOrder Dyadic
  PseudoOrder.strongSetoid pseudoOrderDyadic = strongSetoidDyadic
  PseudoOrder.lt pseudoOrderDyadic = ltDyadic
  PseudoOrder.<-asym pseudoOrderDyadic {x} {y} = <-asym {x = dToQSlow x} {y = dToQSlow y}
  PseudoOrder.<-cotrans pseudoOrderDyadic {x} {y} neq z = <-cotrans {x = dToQSlow x} {y = dToQSlow y} neq (dToQSlow z)
  PseudoOrder.<-total pseudoOrderDyadic x y = <-total (dToQSlow x) (dToQSlow y)
  {-# COMPILE AGDA2HS pseudoOrderDyadic #-}

  shiftLDyadic : ShiftL Dyadic
  ShiftL.semiringa shiftLDyadic = semiRingDyadic
  ShiftL.shiftl shiftLDyadic x n = mant x :|^ (pos n + expo x)
  ShiftL.shiftlProper shiftLDyadic = cheat
  ShiftL.shiftlNull shiftLDyadic = cheat
  ShiftL.shiftlSuc shiftLDyadic = cheat
  {-# COMPILE AGDA2HS shiftLDyadic #-}

  shiftDyadic : Shift Dyadic
  Shift.super shiftDyadic = shiftLDyadic
  Shift.shift shiftDyadic x n = mant x :|^ (n + expo x)
  Shift.shiftProper shiftDyadic = cheat
  Shift.shiftEquivalent shiftDyadic = cheat
  Shift.shiftLeftThenRight shiftDyadic = cheat
  {-# COMPILE AGDA2HS shiftDyadic #-}

  exactShiftDyadic : ExactShift Dyadic
  ExactShift.super exactShiftDyadic = shiftDyadic
  ExactShift.shiftRightThenLeft exactShiftDyadic = cheat
  {-# COMPILE AGDA2HS exactShiftDyadic #-}

  natPowDyadic : Pow Dyadic Nat
  Pow._^_ natPowDyadic x n = (mant x ^ n) :|^ ((pos n) * expo x)
  Pow.powProper natPowDyadic eqx refl = cheat
  Pow.powNull natPowDyadic x = cheat
  Pow.powSuc natPowDyadic x n = cheat
  {-# COMPILE AGDA2HS natPowDyadic #-}

  castDyadicRational : Cast Dyadic Rational
  Cast.cast castDyadicRational x = cast {Int} {Rational} (mant x) * shift (one {Rational}) (expo x)
  {-# COMPILE AGDA2HS castDyadicRational #-}

  castIntDyadic : Cast Int Dyadic
  Cast.cast castIntDyadic k = k :|^ null
  {-# COMPILE AGDA2HS castIntDyadic #-}

  absDyadic : Abs Dyadic
  Abs.ring absDyadic = ringDyadic
  Abs.le absDyadic = leDyadic
  Abs.abs absDyadic x = abs (mant x) :|^ expo x
  Abs.absCorrect absDyadic x = cheat , cheat
  {-# COMPILE AGDA2HS absDyadic #-}
