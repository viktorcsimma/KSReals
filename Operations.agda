-- Type classes for types
-- which have an absolute value, shift etc. operation.

module Operations where

open import Haskell.Prim.Tuple

open import Setoid
open import Ring
open import Order

record Abs (a : Set) : Set₁ where
  field
    overlap {{ring}} : Ring a
    overlap {{le}}   : Le a
    abs : a -> a
    @0 absCorrect : ∀ (x : a) -> (null ≤ x -> abs x ≃ x)
                                × (x ≤ null -> abs x ≃ negate x)
open Abs {{...}} public
{-# COMPILE AGDA2HS Abs class #-}

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

-- Actually, the exponent need not be a Nat; it can also be from a "similar" structure.
record Pow (a : Set) {{semiringa : SemiRing a}} (b : Set) {{semiringb : SemiRing b}}
         : Set₁ where
  infixr 8 _^_
  field
    _^_ : a -> b -> a
    @0 powProper : ∀ {x x' n n'} -> x ≃ x' -> n ≃ n' -> x ^ n ≃ x' ^ n'
    @0 powNull : ∀ x -> x ^ null ≃ one
    @0 powSuc  : ∀ x n -> x ^ (one + n) ≃ x * x ^ n
open Pow {{...}} public
{-# COMPILE AGDA2HS Pow class #-}
