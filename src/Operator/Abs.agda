-- Type classes for types
-- which have an absolute value, shift etc. operation.
{-# OPTIONS --erasure #-}

module Operator.Abs where

open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Order

record Abs (a : Set) : Set₁ where
  field
    overlap {{ring}} : Ring a
    overlap {{le}}   : Le a
    abs : a -> a
    @0 absCorrect : ∀ (x : a) -> (null ≤ x -> abs x ≃ x)
                                × (x ≤ null -> abs x ≃ negate x)
open Abs {{...}} public
{-# COMPILE AGDA2HS Abs class #-}
