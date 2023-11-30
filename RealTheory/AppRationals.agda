-- A type class describing what
-- an implementation of "approximate rationals"
-- should know (it's less then what rationals know).
-- We have an approximate division with a given precision,
-- and an "apprApprox" function.
-- The completion of a type with this class
-- will give the real numbers.
{-# OPTIONS --erasure #-}

module RealTheory.AppRationals where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, const)
import Numeric.Natural

import Algebra.Ring
import Algebra.MetricSpace
import Implementations.Int

#-}

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (id; const)

open import Tools.Cheat

open import Tools.ErasureProduct
open import Algebra.Ring
open import Algebra.Field
open import Algebra.Setoid
open import Operations.Cast
open import Implementations.Rational
open import Algebra.Order
open import Operations.Decidable
open import Operations.Abs
open import Operations.ShiftL
open import Operations.Pow
open import Implementations.Nat
open import Implementations.Int
open import Algebra.MetricSpace
open import Operations.Cast

record AppRationals (aq : Set) : Set₁ where
  field
    -- overlap {{ring}} : Ring aq -- Abs includes this
    overlap {{partialOrder}} : PartialOrder aq
    overlap {{pseudoOrder}} : PseudoOrder aq
    overlap {{decSetoid}} : DecSetoid aq
    overlap {{decLe}} : DecLe aq
    overlap {{decLt}} : DecLt aq
    overlap {{strongSetoid}} : StrongSetoid aq
    overlap {{trivialApart}} : TrivialApart aq
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

open AppRationals {{...}} public
{-# COMPILE AGDA2HS AppRationals class #-}

-- For ease of use,
-- we also derive the cast operator for naturals.
instance
  castNatAQ : ∀{aq}{{araq : AppRationals aq}} -> Cast Nat aq
  Cast.cast castNatAQ n = cast (pos n)
  {-# COMPILE AGDA2HS castNatAQ #-}

instance
  appRationalsRational : AppRationals Rational
  AppRationals.partialOrder appRationalsRational = partialOrderFrac
  AppRationals.pseudoOrder appRationalsRational = pseudoOrderFrac
  AppRationals.decSetoid appRationalsRational = decSetoidFrac
  AppRationals.strongSetoid appRationalsRational = strongSetoidFrac
  AppRationals.trivialApart appRationalsRational = trivialApartFrac
  AppRationals.absAq appRationalsRational = absFrac
  AppRationals.exactShift appRationalsRational = exactShiftFrac {{intShiftL}}
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
  AppRationals.log2Floor appRationalsRational x 0<x = ratLog2Floor x {0<x}
  AppRationals.log2FloorCorrect appRationalsRational = cheat
  {-# COMPILE AGDA2HS appRationalsRational #-}
