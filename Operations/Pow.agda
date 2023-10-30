-- Type classes for types
-- which have an absolute value, shift etc. operation.
{-# OPTIONS --erasure #-}

module Operations.Pow where

open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.Ring

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
