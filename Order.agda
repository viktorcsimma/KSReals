-- Classes and predicates related to ordering.
module Order where

open import Haskell.Prim.Either
open import Haskell.Prim using (⊥)
open import Haskell.Prim.Tuple

open import Relations
open import Setoid

-- A set of which we only know it has a _<_ operator.
-- We need this because we have classes about it that only partially overlap.
record Lt (a : Set) : Set₁ where
  infix 4 _<_
  field
    -- We have to erase this one too.
    @0 _<_ : a -> a -> Set
open Lt {{...}} public
{-# COMPILE AGDA2HS Lt class #-}

record StrictOrder (a : Set) : Set₁ where
  field
    overlap {{lt}} : Lt a
    overlap {{setoid}} : Setoid a
    @0 <-irrefl : Irreflexive _<_
    @0 <-trans  : Transitive _<_
open StrictOrder {{...}} public
{-# COMPILE AGDA2HS StrictOrder class #-}

record StrictSetoidOrder (a : Set) : Set₁ where
  field
    overlap {{setoid}} : Setoid a
    overlap {{strictOrder}} : StrictOrder a
    @0 <-proper : ∀ {x y z w : a} -> x ≃ z -> y ≃ w -> x < y -> z < w
open StrictSetoidOrder {{...}} public
{-# COMPILE AGDA2HS StrictSetoidOrder class #-}

record PseudoOrder (a : Set) : Set₁ where
  field
    overlap {{strongSetoid}} : StrongSetoid a
    overlap {{lt}} : Lt a
    @0 <-asym : Asymmetric _<_
    @0 <-cotrans : ∀ (x y z : a) -> x < y -> Either (x < z) (z < y)
    @0 <-total : ∀ (x y : a) -> x >< y ↔ Either (x < y) (y < x)
  @0 _>_ : a -> a -> Set
  x > y = y < x
open PseudoOrder {{...}} public
{-# COMPILE AGDA2HS PseudoOrder class #-}

--  Now we try to skip some parts.

record TrivialApart (a : Set) : Set₁ where
  field
    overlap {{super}} : StrongSetoid a
    @0 trivialApart : ∀ (x y : a) -> x >< y ↔ (x ≃ y -> ⊥)
open TrivialApart {{...}} public
{-# COMPILE AGDA2HS TrivialApart class #-}

@0 StrictOrderEmbedding : {a b : Set} -> {{PseudoOrder a}} -> {{PseudoOrder b}}
                                 -> (a -> b) -> Set
StrictOrderEmbedding {a} f = SetoidMorphism f  -- I didn't quite understand what the difference is between this and StrictSetoidMorphism
                                  × ∀ {x y : a} -> x < y -> f x < f y
                                  × ∀ {x y : a} -> f x < f y -> x < y
