-- Definitions and type classes about decidable propositions,
-- equality, ordering etc.
{-# OPTIONS --erasure #-}

module Operator.Decidable where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Haskell.Prim.Either
open import Haskell.Prim using (IsTrue; if_then_else_)

open import Algebra.Setoid
open import Tool.Relations
open import Algebra.Order

-- In order to make it compilable, we always define operators
-- that return Bools; instead of using P ⊎ ¬ P.

@0 DecidesBinary : ∀ {a : Set} -> (a -> a -> Bool) -> (a -> a -> Set) -> Set
DecidesBinary {a} _###_ _##_ = ∀ (x y : a) -> IsTrue (x ### y) ↔ (x ## y)

-- The suffix of the operator will always be #
-- (that's what Haskell supports
-- and which is (hopefully) not used elsewhere).

record DecSetoid (a : Set) : Set₁ where
  infix 4 _≃#_
  field
    overlap {{setoid}} : Setoid a
    _≃#_ : a -> a -> Bool
    @0 ≃#-correct : DecidesBinary _≃#_ _≃_
open DecSetoid {{...}} public
{-# COMPILE AGDA2HS DecSetoid class #-}

record DecLe (a : Set) : Set₁ where
  infix 4 _≤#_
  field
    overlap {{le}} : Le a
    _≤#_ : a -> a -> Bool
    @0 ≤#-correct : DecidesBinary _≤#_ _≤_
open DecLe {{...}} public
{-# COMPILE AGDA2HS DecLe class #-}

record DecLt (a : Set) : Set₁ where
  infix 4 _<#_
  field
    overlap {{lt}} : Lt a
    _<#_ : a -> a -> Bool
    @0 <#-correct : DecidesBinary _<#_ _<_
open DecLt {{...}} public
{-# COMPILE AGDA2HS DecLt class #-}

max min : ∀ {a : Set} {{declt : DecLt a}} -> a -> a -> a
max x y = if x <# y then y else x
min x y = if x <# y then x else y
{-# COMPILE AGDA2HS max #-}
{-# COMPILE AGDA2HS min #-}
