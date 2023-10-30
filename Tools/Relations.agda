-- Some useful properties of relations
-- and propositions.
{-# OPTIONS --erasure #-}

module Tools.Relations where

open import Agda.Primitive
open import Haskell.Prim.Tuple
open import Haskell.Prim using (⊥)

-- Logical equivalence.
infix 2 _↔_
_↔_ : Set -> Set -> Set
a ↔ b = (a -> b) × (b -> a)
{-# COMPILE AGDA2HS _↔_ #-}

-- An Either which can be used for any levels.
data _⊎_ {i j} (a : Set i) (b : Set j) : Set (i ⊔ j) where
  inl : a -> a ⊎ b
  inr : b -> a ⊎ b

@0 Reflexive Transitive Cotransitive Symmetric Asymmetric :
                    ∀ {i} {a : Set i} -> (a -> a -> Set i) -> Set i

-- We follow the standard library by not using the equality at Reflexive,
-- by using it at Irreflexive.
Reflexive {a = a} r = ∀ {x : a} -> r x x
Transitive {a = a} r = ∀ {x y z : a} -> r x y -> r y z -> r x z
Cotransitive {a = a} r = ∀ {x y : a} → r x y → ∀ (z : a) → (r x z) ⊎ (r z y)
Symmetric {a = a} r = ∀ {x y : a} -> r x y -> r y x
-- In Coq, this is a strict asymmetric property. So they cannot even be equal.
Asymmetric {a = a} r = ∀ {x y : a} -> r x y -> r y x -> ⊥
