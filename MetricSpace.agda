-- Definition of metric and prelength spaces.
module MetricSpace where

open import Cheat

open import Haskell.Prim.Tuple

open import ErasureProduct
open import Setoid
open import Ring
open import Int
open import Rational
open import Order
open import Operations

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

-- Here come the instances for Rational to avoid back-and-forth references.
instance
  metricSpaceRational : MetricSpace Rational
  MetricSpace.ball metricSpaceRational ε x y = abs (x + negate y) ≤ proj₁ ε
  MetricSpace.ballReflexive metricSpaceRational = cheat
  MetricSpace.ballSym metricSpaceRational = cheat
  MetricSpace.ballTriangle metricSpaceRational = cheat
  MetricSpace.ballClosed metricSpaceRational = cheat
  MetricSpace.ballEq metricSpaceRational = cheat
  {-# COMPILE AGDA2HS metricSpaceRational #-}
