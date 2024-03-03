-- Definition of metric and prelength spaces.
{-# OPTIONS --erasure #-}

module RealTheory.MetricSpace where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, Bool(..))
import Numeric.Natural

-- these are mostly needed for the foreign pragmas
import Algebra.SemiRing
import Algebra.Ring
import Operator.Abs
import Operator.Shift
import Implementation.Int
import Implementation.Rational
import Implementation.Dyadic
#-}

open import Tool.Cheat

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int
open import Haskell.Prim.Tuple
open import Haskell.Prim using (if_then_else_; the)

open import Tool.ErasureProduct
open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Implementation.Dyadic
open import Algebra.Order
open import Operator.Abs
open import Operator.Decidable
open import Operator.ShiftL
open import Operator.Shift

record MetricSpace (a : Set) : Set₁ where
  field
    overlap {{setoid}} : Setoid a
    -- This is the concrete Rational type.
    -- It cannot deduce ε; so it's an explicit argument.
    @0 ball : PosRational -> a -> a -> Set
    @0 ballReflexive : ∀ (ε : PosRational) -> ∀ x x'
                            -> x ≃ x' -> ball ε x x'
    @0 ballSym : ∀ (ε : PosRational) -> ∀ x y
                            -> ball ε x y -> ball ε y x
    @0 ballTriangle : ∀ (ε₁ ε₂ : PosRational) -> ∀ x y z
                            -> ball ε₁ x y -> ball ε₂ y z
                            -> ball (plusPos ε₁ ε₂) x y
    @0 ballClosed : ∀ (ε : PosRational) -> ∀ x y
                            -> (∀ (δ : PosRational) -> ball (plusPos ε δ) x y)
                            -> ball ε x y
    @0 ballEq : ∀ x y -> (∀ (ε : PosRational) -> ball ε x y)
                            -> x ≃ y
open MetricSpace {{...}} public
{-# COMPILE AGDA2HS MetricSpace class #-}

record PrelengthSpace (a : Set) : Set₁ where
  field
    overlap {{metricSpace}} : MetricSpace a
    -- here there is an existential quantifier; so this won't be erased
    prelength : ∀ (ε δ₁ δ₂ : PosRational) -> ∀ x y
                      -> @0 (proj₁ ε < proj₁ δ₁ + proj₁ δ₂)
                      -> @0 (ball ε x y)
                      -> Σ0 a (λ z -> ball δ₁ x z × ball δ₂ z y) 
open PrelengthSpace {{...}} public
{-# COMPILE AGDA2HS PrelengthSpace class #-}

-- | a/b - c/d | <= ε
-- | a*d - c*b | <= b*d*ε
-- Hm... maybe we'll have to restrict ourselves to the rationals instead of all fractions.

-- Here come the instances for Rational and Dyadic
-- to avoid back-and-forth references.
instance
  metricSpaceRational : MetricSpace Rational
  MetricSpace.ball metricSpaceRational ε x y = abs (x + negate y) ≤ proj₁ ε
  MetricSpace.ballReflexive metricSpaceRational = cheat
  MetricSpace.ballSym metricSpaceRational = cheat
  MetricSpace.ballTriangle metricSpaceRational = cheat
  MetricSpace.ballClosed metricSpaceRational = cheat
  MetricSpace.ballEq metricSpaceRational = cheat
  {-# COMPILE AGDA2HS metricSpaceRational #-}

  prelengthSpaceRational : PrelengthSpace Rational
  PrelengthSpace.metricSpace prelengthSpaceRational = metricSpaceRational
  PrelengthSpace.prelength prelengthSpaceRational
                 ε δ₁ δ₂ x y ε<δ₁+δ₂ bεxy
                    = if (x ≤# y)
                       then x + proj₁ δ₁ :&: cheat
                       else y + proj₁ δ₁ :&: cheat
  {-# COMPILE AGDA2HS prelengthSpaceRational #-}

  metricSpaceDyadic : MetricSpace Dyadic
  MetricSpace.setoid metricSpaceDyadic = setoidDyadic
  MetricSpace.ball metricSpaceDyadic ε x y = ball ε (dToQSlow x) (dToQSlow y)
  MetricSpace.ballReflexive metricSpaceDyadic ε x x' eq
      = ballReflexive ε (dToQSlow x) (dToQSlow x') eq
  MetricSpace.ballSym metricSpaceDyadic ε x y x≤y
      = ballSym ε (dToQSlow x) (dToQSlow y) x≤y
  MetricSpace.ballTriangle metricSpaceDyadic ε₁ ε₂ x y z x≤y y≤z
      = ballTriangle ε₁ ε₂ (dToQSlow x) (dToQSlow y) (dToQSlow z) x≤y y≤z
  MetricSpace.ballClosed metricSpaceDyadic ε x y f
      = ballClosed ε (dToQSlow x) (dToQSlow y) f
  MetricSpace.ballEq metricSpaceDyadic x y f = ballEq (dToQSlow x) (dToQSlow y) f
  {-# COMPILE AGDA2HS metricSpaceDyadic #-}

  {-# TERMINATING #-}
  prelengthSpaceDyadic : PrelengthSpace Dyadic
  PrelengthSpace.metricSpace prelengthSpaceDyadic = metricSpaceDyadic
  PrelengthSpace.prelength prelengthSpaceDyadic     eps
                                                    d1
                                                    d2
                                                    x y
                                                    ε<δ₁+δ₂
                                                    bεxy
  -- We'll use an iterative method: we always add the lowest 2-power
  -- we can to approximate x+δ₁ (or x-δ₁).
      = go x goal (x ≤# y) currPrec steps :&: (cheat , cheat)
     where
     goal : Rational
     goal = if x ≤# y
            then dToQSlow x + proj₁ d1
            else dToQSlow x + negate (proj₁ d1)
     approx : PosRational -> Int   -- an exponent of 2 for which q<=2^k
     approx q = pos (goApprox (proj₁ q) 0)
       where
       goApprox : Rational -> Nat -> Nat
       goApprox q n = if q ≤# one then n
                        else goApprox (shift q (the Int (negsuc 0))) (1 + n)
     currPrec : Int
     currPrec = approx d1
     desiredPrec : Int
     desiredPrec = approx (proj₁ d1 + proj₁ d2 + negate (proj₁ eps)
                             :&: cheat)
     steps : Nat
     steps = if currPrec ≤# desiredPrec then 0 else natAbs (currPrec + negate desiredPrec)

     go : (d : Dyadic) (q : Rational) (isAbove : Bool)
             (currentPrecision : Int) (remainingSteps : Nat) -> Dyadic
            -- ^ this is the exponent of 2
            -- and remainingSteps means how many times we need to subtract one from it
     go d _ _ _ zero = d
     go d q isAbove currPrec (suc n) =
             if (abs ((dToQSlow d) + negate q) ≤# shift one (negsuc 0 + currPrec))
             then go d q isAbove (negsuc 0 + currPrec) n
             else go (d + step isAbove currPrec) q isAbove (negsuc 0 + currPrec) n
       where
       step : Bool -> Int -> Dyadic
       step true  currPrec = pos 1    :|^ (negsuc 0 + currPrec)
       step false currPrec = negsuc 0 :|^ (negsuc 0 + currPrec)
  -- Again suc...
  {-# FOREIGN AGDA2HS
  instance PrelengthSpace Dyadic where
    prelength eps d1 d2 x y = (go x goal (x ≤# y) currPrec steps :&:)
      where
        goal :: Rational
        goal
          = if x ≤# y then dToQSlow x + proj₁ d1 else
              dToQSlow x + negate (proj₁ d1)
        approx :: PosRational -> Integer
        approx q = pos (goApprox (proj₁ q) 0)
          where
            goApprox :: Rational -> Natural -> Natural
            goApprox q n
              = if q ≤# one then n else goApprox (shift q (negsuc 0)) (1 + n)
        currPrec :: Integer
        currPrec = approx d1
        desiredPrec :: Integer
        desiredPrec = approx (proj₁ d1 + proj₁ d2 + negate (proj₁ eps) :&:)
        steps :: Natural
        steps
          = if currPrec ≤# desiredPrec then 0 else
              natAbs (currPrec + negate desiredPrec)
        go :: Dyadic -> Rational -> Bool -> Integer -> Natural -> Dyadic
        go d _ _ _ 0 = d
        go d q isAbove currPrec sn =
                if (abs ((dToQSlow d) + negate q) ≤# shift one (negate 1 + currPrec))
                then go d q isAbove (negate 1 + currPrec) (sn Prelude.- 1)
                else go (d + step isAbove currPrec) q isAbove (negate 1 + currPrec) (sn Prelude.- 1)
          where
          step :: Bool -> Integer -> Dyadic
          step True  currPrec = 1         :|^ (negate 1 + currPrec)
          step False currPrec = negate 1  :|^ (negate 1 + currPrec)
  #-}
