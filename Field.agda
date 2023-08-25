-- The Field class.
module Field where

open import Setoid
open import Ring

record Field (a : Set) : Set₁ where
  field
    overlap {{ring}} : Ring a
    overlap {{strongSetoid}} : StrongSetoid a
    @0 +-strong-proper : StrongSetoidBinaryMorphism _+_
    @0 *-strong-proper : StrongSetoidBinaryMorphism _*_

    @0 nullNeqOne : null >< one

    recip : (x : a) -> @0 (x >< null) -> a
    -- I don't know yet how we could use SetoidMorphism here; the x><0 argument makes this hard.
    @0 recip-proper : ∀ {x y : a} (x><null : x >< null) (y><null : y >< null)
                               -> x ≃ y -> recip x x><null ≃ recip y y><null
    @0 *-inverseˡ : ∀ {x : a} (x><null : x >< null) -> recip x x><null * x ≃ one
    @0 *-inverseʳ : ∀ {x : a} (x><null : x >< null) -> x * recip x x><null ≃ one
open Field {{...}} public
{-# COMPILE AGDA2HS Field class #-}
