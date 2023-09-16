-- A type class describing what
-- an implementation of "approximate rationals"
-- should know (it's less then what rationals know).
-- We have an approximate division with a given precision,
-- and an "apprApprox" function.
-- The completion of a type with this class
-- will give the real numbers.

module AppRationals where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim using (id; const)

open import Cheat

open import ErasureProduct
open import Ring
open import Field
open import Setoid
open import Cast
open import Rational
open import Order
open import Decidable
open import Operations
open import Nat
open import Int
open import MetricSpace
open import Cast

record AppRationals (aq : Set) : Set₁ where
  field
    overlap {{ring}} : Ring aq
    overlap {{partialOrder}} : PartialOrder aq
    overlap {{pseudoOrder}} : PseudoOrder aq
    overlap {{decLe}} : DecLe aq
    overlap {{decLt}} : DecLt aq
    overlap {{strongSetoid}} : StrongSetoid aq
    overlap {{trivialApart}} : TrivialApart aq
    overlap {{absAq}} : Abs aq
    overlap {{shiftL}} : ShiftL aq Int
    overlap {{natPow}} : Pow aq Nat
    overlap {{castAqRational}} : Cast aq Rational
    overlap {{castIntAq}} : Cast Int aq

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
                            -> ball (shiftl one k :&: cheat)   -- 2 ^ k
                                    (cast {aq} {Rational} (appDiv x y NonZeroy k))
                                    (cast {aq} {Rational} x * recip (cast {aq} {Rational} y) (aqNonZeroToNonZero NonZeroy))

    -- A function "compressing" an AQ to a more easily representable AQ,
    -- within a given range.
    appApprox : aq -> Int -> aq
    @0 appApproxCorrect : ∀ x k -> ball (shiftl one k :&: cheat)
                                   (cast {aq} {Rational} (appApprox x k))
                                   (cast {aq} {Rational} x)

    -- cast is a given conversion from any Int to AQ (see the Cast Int aq instance above).
    @0 intToAqSemiRingMorphism : SemiRingMorphism {{semiRinga = semiRingInt}} (cast {Int} {aq})

open AppRationals {{...}} public
{-# COMPILE AGDA2HS AppRationals class #-}

instance
  appRationalsRational : AppRationals Rational
  AppRationals.ring appRationalsRational = ringFrac
  AppRationals.partialOrder appRationalsRational = partialOrderFrac
  AppRationals.pseudoOrder appRationalsRational = pseudoOrderFrac
  AppRationals.strongSetoid appRationalsRational = strongSetoidFrac
  AppRationals.trivialApart appRationalsRational = trivialApartFrac
  AppRationals.absAq appRationalsRational = absFrac
  AppRationals.shiftL appRationalsRational = shiftLFrac
  AppRationals.natPow appRationalsRational = natPowFrac
  AppRationals.castAqRational appRationalsRational = castSame
  AppRationals.castIntAq appRationalsRational = castFrac
  AppRationals.aqToQOrderEmbed appRationalsRational = cheat
  AppRationals.aqToQStrictOrderEmbed appRationalsRational = cheat
  AppRationals.aqToQSemiRingMorphism appRationalsRational = cheat
  AppRationals.aqNonZeroToNonZero appRationalsRational = id
  AppRationals.appDiv appRationalsRational x y NonZeroy _ = x * recip y NonZeroy
  AppRationals.appDivCorrect appRationalsRational = cheat
  AppRationals.appApprox appRationalsRational = const
  AppRationals.appApproxCorrect appRationalsRational = cheat
  AppRationals.intToAqSemiRingMorphism appRationalsRational = cheat
  {-# COMPILE AGDA2HS appRationalsRational #-}
