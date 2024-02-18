-- The Field and DecField classes.
{-# OPTIONS --erasure #-}

module Algebra.Field where

open import Haskell.Prim using (⊥)

open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring

record Field (a : Set) : Set₁ where
  field
    overlap {{ring}} : Ring a
    overlap {{strongSetoid}} : StrongSetoid a
    @0 +-strong-proper : StrongSetoidBinaryMorphism _+_
    @0 *-strong-proper : StrongSetoidBinaryMorphism _*_

    recip : (x : a) -> @0 NonZero x -> a
    -- I don't know yet how we could use SetoidMorphism here; the x><0 argument makes this hard.
    @0 recip-proper : ∀ {x y : a} (NonZerox : NonZero x) (NonZeroy : NonZero y)
                               -> x ≃ y -> recip x NonZerox ≃ recip y NonZeroy
    @0 *-inverseˡ : ∀ {x : a} (NonZerox : NonZero x) -> recip x NonZerox * x ≃ one
    @0 *-inverseʳ : ∀ {x : a} (NonZerox : NonZero x) -> x * recip x NonZerox ≃ one
open Field {{...}} public
{-# COMPILE AGDA2HS Field class #-}

{-
-- DecField is a field in which the reciprocal function is total.
record DecField (a : Set) : Set₁ where
  field
    overlap {{ring}} : Ring a
    decRecip : a -> a
    @0 decRecipProper : SetoidMorphism decRecip
    @0 decRecipInverse : ∀ (x : a) -> (x ≃ null -> ⊥) -> x * decRecip x ≃ one
    -- We let /0 = 0 so properties as Injective (/), f (/x) = / (f x), / /x = x, /x * /y = /(x * y) 
    -- hold without any additional assumptions.
    @0 decRecipNull : decRecip null ≃ null
open DecField {{...}} public
{-# COMPILE AGDA2HS DecField #-}
-}
