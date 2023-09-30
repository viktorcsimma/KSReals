-- Type classes for types
-- which have an absolute value, shift etc. operation.

module Operations.ShiftL where

open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.Ring

record ShiftL (a b : Set) : Set₁ where
  field
    overlap {{semiringa}} : SemiRing a
    overlap {{semiringb}} : SemiRing b
    shiftl : a -> b -> a
    @0 shiftlProper : ∀ (x x' : a) (y y' : b)
                           -> x ≃ x' -> y ≃ y' -> shiftl x y ≃ shiftl x' y'
    @0 shiftlNull : ∀ (x : a) -> shiftl x null ≃ x
    @0 shiftlSuc : ∀ (x : a) (y : b) -> shiftl x (one + y) ≃ shiftl ((one + one) * x) y
open ShiftL {{...}} public
{-# COMPILE AGDA2HS ShiftL class #-}
