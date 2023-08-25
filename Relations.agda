-- Some useful properties of relations
-- and propositions.

module Relations where

open import Haskell.Prim.Tuple
open import Haskell.Prim using (⊥)
open import Haskell.Prim.Either

-- Logical equivalence.
infix 2 _↔_
_↔_ : Set -> Set -> Set
a ↔ b = (a -> b) × (b -> a)
{-# COMPILE AGDA2HS _↔_ #-}

@0 Reflexive : {a : Set} -> (a -> a -> Set) -> Set
Reflexive {a} r = ∀ {x : a} -> r x x

@0 Irreflexive : {a : Set} -> (a -> a -> Set) -> Set
Irreflexive {a} r = ∀ {x : a} -> r x x -> ⊥

@0 Transitive : {a : Set} -> (a -> a -> Set) -> Set
Transitive {a} r = ∀ {x y z : a} -> r x y -> r y z -> r x z

@0 Cotransitive : {a : Set} -> (a -> a -> Set) -> Set
Cotransitive {a} r = ∀ {x y : a} → r x y → ∀ (z : a) → Either (r x z) (r z y)

@0 Symmetric : {a : Set} -> (a -> a -> Set) -> Set
Symmetric {a} r = ∀ {x y : a} -> r x y -> r y x

-- In Coq, this is a strict asymmetric property. So they cannot even be equal.
@0 Asymmetric : {a : Set} -> (a -> a -> Set) -> Set
Asymmetric {a} r = ∀ {x y : a} -> r x y -> r y x -> ⊥
