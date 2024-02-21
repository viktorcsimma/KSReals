-- A type class describing what
-- an implementation of "approximate rationals"
-- should know (it's less then what rationals know).
-- We have an approximate division with a given precision,
-- and an "apprApprox" function.
-- The completion of a type with this class
-- will give the real numbers.
{-# OPTIONS --erasure #-}

module RealTheory.AppRational where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, const)
import Numeric.Natural

import Algebra.SemiRing
import Algebra.Ring
import RealTheory.MetricSpace
import Implementation.Int

#-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (id; const)

open import Tool.Cheat

open import Tool.ErasureProduct
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Field
open import Algebra.Setoid
open import Operator.Cast
open import Implementation.Frac
open import Implementation.Rational
open import Algebra.Order
open import Operator.Decidable
open import Operator.Abs
open import Operator.ShiftL
open import Operator.Shift
open import Operator.ExactShift
open import Operator.Pow
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Dyadic
open import Implementation.Decimal
open import RealTheory.MetricSpace
open import Operator.Cast

record AppRational (aq : Set) : Set₁ where
  field
    -- overlap {{ring}} : Ring aq -- Abs includes this
    overlap {{partialOrder}} : PartialOrder aq
    overlap {{pseudoOrder}} : PseudoOrder aq
    overlap {{decSetoid}} : DecSetoid aq
    overlap {{decLe}} : DecLe aq
    overlap {{decLt}} : DecLt aq
    overlap {{strongSetoid}} : StrongSetoid aq
    overlap {{absAq}} : Abs aq -- we need this for alternating series
    overlap {{exactShift}} : ExactShift aq
    overlap {{natPow}} : Pow aq Nat
    overlap {{castAqRational}} : Cast aq Rational
    overlap {{castIntAq}} : Cast Int aq
    -- We write PrelengthSpace here;
    -- it is not necessary for the conditions,
    -- but needed later.
    overlap {{prelengthAq}} : PrelengthSpace aq

    -- Here, cast is a conversion to the "original" rationals.
    @0 aqToQOrderEmbed : OrderEmbedding (cast {aq} {Rational})
    @0 aqToQStrictOrderEmbed : StrictOrderEmbedding (cast {aq} {Rational})
    @0 aqToQSemiRingMorphism : SemiRingMorphism (cast {aq} {Rational})
    -- @0 aqDenseEmbedding : DenseEmbedding aqToQ
    -- For the sake of simplicity, we also require this:
    @0 aqNonZeroToNonZero : ∀ {x : aq} -> NonZero x -> NonZero (cast {aq} {Rational} x)

    -- appDiv is an approximate division operator with a given precision.
    -- The error is at most 2ᵏ.
    -- We stay with the concrete Int representation for now.
    -- And we don't require it to be nonzero.
    appDiv : (x y : aq) -> @0 (NonZero y) -> Int -> aq
    @0 appDivCorrect : ∀ (x y : aq) (NonZeroy : NonZero y) (k : Int)
                            -> ball (shift one k :&: cheat)   -- 2 ^ k
                                    (cast {aq} {Rational} (appDiv x y NonZeroy k))
                                    (cast {aq} {Rational} x * recip (cast {aq} {Rational} y) (aqNonZeroToNonZero NonZeroy))

    -- A function "compressing" an AQ to a more easily representable AQ,
    -- within a given range.
    appApprox : aq -> Int -> aq
    @0 appApproxCorrect : ∀ x k -> ball (shift one k :&: cheat)
                                   (cast {aq} {Rational} (appApprox x k))
                                   (cast {aq} {Rational} x)

    -- cast is a given conversion from any Int to AQ (see the Cast Int aq instance above).
    @0 intToAqSemiRingMorphism : SemiRingMorphism {{semiRinga = semiRingInt}} (cast {Int} {aq})

    -- and to be able to provide a representation-dependent implementation of log₂:
    log2Floor : (x : aq) -> @0 (null < x) -> Int
    @0 log2FloorCorrect : ∀ (x : aq) (@0 0<x : null < x)
                                      -> shift one (log2Floor x 0<x) ≤ x
                                          × x < shift one (pos 1 + (log2Floor x 0<x))

    -- finally, to be able to print them in decimal form
    -- (with a given precision of digits
    --      after the decimal point):
    toDecimal : (x : aq) (prec : Nat) -> Decimal
    @0 toDecimalCorrect : ∀ x prec ->
                            (cast {aq} {Rational} x) - (cast {Decimal} {Rational} (toDecimal x prec))
                                < MkFrac (pos 1) (pos (2 * 10 ^ prec)) cheat

open AppRational {{...}} public
{-# COMPILE AGDA2HS AppRational class #-}

-- For ease of use,
-- we also derive the cast operator for naturals.
instance
  castNatAQ : ∀{aq}{{araq : AppRational aq}} -> Cast Nat aq
  Cast.cast castNatAQ n = cast (pos n)
  {-# COMPILE AGDA2HS castNatAQ #-}

instance
  appRationalRational : AppRational Rational
  AppRational.partialOrder appRationalRational = partialOrderFrac
  AppRational.pseudoOrder appRationalRational = pseudoOrderFrac
  AppRational.decSetoid appRationalRational = decSetoidFrac
  AppRational.strongSetoid appRationalRational = strongSetoidFrac
  AppRational.absAq appRationalRational = absFrac
  AppRational.exactShift appRationalRational = exactShiftFrac {{intShiftL}}
  AppRational.natPow appRationalRational = natPowFrac
  AppRational.castAqRational appRationalRational = castSame
  AppRational.castIntAq appRationalRational = castFrac
  AppRational.aqToQOrderEmbed appRationalRational = cheat
  AppRational.aqToQStrictOrderEmbed appRationalRational = cheat
  AppRational.aqToQSemiRingMorphism appRationalRational = cheat
  AppRational.aqNonZeroToNonZero appRationalRational = id
  AppRational.appDiv appRationalRational x y NonZeroy _ = x * recip y NonZeroy
  AppRational.appDivCorrect appRationalRational = cheat
  AppRational.appApprox appRationalRational = const
  AppRational.appApproxCorrect appRationalRational = cheat
  AppRational.intToAqSemiRingMorphism appRationalRational = cheat
  AppRational.log2Floor appRationalRational x 0<x = ratLog2Floor x {0<x}
  AppRational.log2FloorCorrect appRationalRational = cheat
  AppRational.toDecimal appRationalRational = rationalToDecimal
  AppRational.toDecimalCorrect appRationalRational = cheat
  {-# COMPILE AGDA2HS appRationalRational #-}

  -- And now...
  appRationalDyadic : AppRational Dyadic
  AppRational.partialOrder appRationalDyadic = partialOrderDyadic
  AppRational.pseudoOrder appRationalDyadic = pseudoOrderDyadic
  AppRational.decSetoid appRationalDyadic = decSetoidDyadic
  AppRational.strongSetoid appRationalDyadic = strongSetoidDyadic
  AppRational.absAq appRationalDyadic = absDyadic
  AppRational.exactShift appRationalDyadic = exactShiftDyadic
  AppRational.natPow appRationalDyadic = natPowDyadic
  AppRational.castAqRational appRationalDyadic = castDyadicRational
  AppRational.castIntAq appRationalDyadic = castIntDyadic
  AppRational.prelengthAq appRationalDyadic = prelengthSpaceDyadic


  AppRational.aqToQOrderEmbed appRationalDyadic = ((λ _ _ eq -> eq) , λ _ _ le -> le) , ((λ _ _ eq -> eq) , λ _ _ le -> le)
  AppRational.aqToQStrictOrderEmbed appRationalDyadic = ((λ _ _ eq -> eq) , id) , id
  setoidMorphism (SemiRingMorphism.preserves-+ (AppRational.aqToQSemiRingMorphism appRationalDyadic)) = λ _ _ eq -> eq
  preservesOp (SemiRingMorphism.preserves-+ (AppRational.aqToQSemiRingMorphism appRationalDyadic)) x y = cheat -- here, we could use the Rational instance
  setoidMorphism (SemiRingMorphism.preserves-* (AppRational.aqToQSemiRingMorphism appRationalDyadic)) = λ _ _ eq -> eq
  preservesOp (SemiRingMorphism.preserves-* (AppRational.aqToQSemiRingMorphism appRationalDyadic)) x y = cheat
  SemiRingMorphism.preserves-null (AppRational.aqToQSemiRingMorphism appRationalDyadic) = refl
  SemiRingMorphism.preserves-one (AppRational.aqToQSemiRingMorphism appRationalDyadic) = refl
  AppRational.aqNonZeroToNonZero appRationalDyadic {pos (suc n) :|^ expo₁} NonZerox = cheat
  AppRational.aqNonZeroToNonZero appRationalDyadic {negsuc n :|^ expo₁} NonZerox = cheat

  -- https://github.com/coq-community/corn/blob/c08a0418f97a04ea7a6cdc3a930561cc8fc84d82/reals/faster/ARbigD.v#L265
  -- (shift (mant x) (- (k-1) + expo x - expo y)) `quot` mant y :|^ (k-1)
  AppRational.appDiv appRationalDyadic x y NonZeroy k
      = intQuot (shift (mant x) (negate k + pos 1 + expo x + negate (expo y))) (mant y) NonZeroy :|^ (k - pos 1)
  AppRational.appDivCorrect appRationalDyadic = cheat

  -- Actually, we wouldn't have to shift if we shifted leftwards, would we?
  AppRational.appApprox appRationalDyadic x k = shift (mant x) (expo x - k + pos 1) :|^ (k - pos 1)
  AppRational.appApproxCorrect appRationalDyadic = cheat

  setoidMorphism (SemiRingMorphism.preserves-+ (AppRational.intToAqSemiRingMorphism appRationalDyadic)) _ _ refl = refl
  preservesOp (SemiRingMorphism.preserves-+ (AppRational.intToAqSemiRingMorphism appRationalDyadic)) _ _ = cheat
  setoidMorphism (SemiRingMorphism.preserves-* (AppRational.intToAqSemiRingMorphism appRationalDyadic)) _ _ refl = refl
  preservesOp (SemiRingMorphism.preserves-* (AppRational.intToAqSemiRingMorphism appRationalDyadic)) _ _ = cheat
  SemiRingMorphism.preserves-null (AppRational.intToAqSemiRingMorphism appRationalDyadic) = refl
  SemiRingMorphism.preserves-one (AppRational.intToAqSemiRingMorphism appRationalDyadic) = refl

  AppRational.log2Floor appRationalDyadic (m :|^ k) 0<x = pos (natLog2Floor (natAbs m) {cheat}) + k
  -- AppRational.log2Floor appRationalDyadic (negsuc n :|^ k) 0<x = {!!} -- we should derive a contradiction here
  AppRational.log2FloorCorrect appRationalDyadic = cheat

  AppRational.toDecimal appRationalDyadic = dyadicToDecimal
  AppRational.toDecimalCorrect appRationalDyadic = cheat

  {-# COMPILE AGDA2HS appRationalDyadic #-}
