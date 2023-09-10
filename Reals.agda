-- Some common operations on real number types
-- (AppRationals types in the C monad).
module Reals where

open import Haskell.Prim using (id)

open import Setoid
open import Rational
open import AppRationals
open import MetricSpace
open import Continuity
open import Ring
open import Field
open import Complete

instance
  semiRingReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> SemiRing (C a)
  SemiRing.super semiRingReals = setoidC
  -- TODO: we should rewrite this with map2.
  SemiRing._+_ (semiRingReals {a} {{pra = pra}}) x y
                                 = (x #>>= λ x ->
                                   (y #>>= λ y ->
                                   returnC (x + y))
                                        (WrapMod id λ ε y₁ y₂ bεxy δ₁ δ₂ ->
                                              ballReflexive (plusPos (plusPos ε δ₁) δ₂) (x + y₁) (x + y₁) (≃-refl {a} {{MetricSpace.setoid (PrelengthSpace.metricSpace pra)}} {x + y₁})))
                                        (WrapMod id λ ε y₁ y₂ bεxy δ₁ δ₂ -> {!!})
  SemiRing._*_ semiRingReals = {!!}
  SemiRing.+-proper semiRingReals = {!!}
  SemiRing.+-assoc semiRingReals = {!!}
  SemiRing.*-proper semiRingReals = {!!}
  SemiRing.*-assoc semiRingReals = {!!}
  SemiRing.null semiRingReals = {!!}
  SemiRing.one semiRingReals = {!!}
  SemiRing.NonZero semiRingReals = {!!}
  SemiRing.NonZeroCorrect semiRingReals = {!!}
  SemiRing.NonZeroOne semiRingReals = {!!}
  SemiRing.+-identityˡ semiRingReals = {!!}
  SemiRing.+-identityʳ semiRingReals = {!!}
  SemiRing.*-identityˡ semiRingReals = {!!}
  SemiRing.*-identityʳ semiRingReals = {!!}
  SemiRing.+-comm semiRingReals = {!!}
  SemiRing.*-comm semiRingReals = {!!}
  SemiRing.*-nullˡ semiRingReals = {!!}
  SemiRing.*-nullʳ semiRingReals = {!!}
  SemiRing.*-distribˡ-+ semiRingReals = {!!}
  SemiRing.*-distribʳ-+ semiRingReals = {!!}
  {-# COMPILE AGDA2HS semiRingReals #-}
