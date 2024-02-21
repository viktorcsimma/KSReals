-- The Setoid and StrongSetoid classes
-- and some useful properties of functions on them.
{-# OPTIONS --erasure #-}

module Algebra.Setoid where

open import Haskell.Prim using (⊥)
open import Haskell.Prim.Tuple
open import Haskell.Prim.Either

open import Tool.Relation

record Setoid (a : Set) : Set₁ where
  infix 3 _≃_
  field
    @0 _≃_ : a -> a -> Set
    @0 ≃-refl : Reflexive _≃_
    @0 ≃-sym  : Symmetric _≃_
    @0 ≃-trans : Transitive _≃_
open Setoid {{...}} public
{-# COMPILE AGDA2HS Setoid class #-}

-- Some other shortenings which depend on _≃_.

@0 Irreflexive : {a : Set} -> {{Setoid a}} -> (a -> a -> Set) -> Set
Irreflexive {a = a} r = ∀ {x y : a} -> x ≃ y -> r x y -> ⊥

-- These _don't_ assume the respective functions are morphisms.
@0 Injective : {a b : Set} -> {{Setoid a}} -> {{Setoid b}} -> (a -> b) -> Set
Injective {a} f = ∀ (x y : a) -> f x ≃ f y -> x ≃ y

@0 Associative : {a : Set} -> {{Setoid a}} -> (a -> a -> a) -> Set
Associative {a} _#_ = ∀ (x y z : a) -> (x # y) # z ≃ x # (y # z)

@0 Commutative : {a : Set} -> {{Setoid a}} -> (a -> a -> a) -> Set
Commutative {a} _#_ = ∀ (x y : a) -> x # y ≃ y # x

-- Now morphism itself.
@0 SetoidMorphism : {a b : Set} -> {{Setoid a}} -> {{Setoid b}}
                                   -> (a -> b) -> Set
SetoidMorphism {a} f = ∀ (x y : a) -> x ≃ y -> f x ≃ f y

-- For binary operators on a.
@0 SetoidBinaryMorphism : {a b : Set} -> {{Setoid a}} -> {{Setoid b}}
                                   -> (a -> a -> b) -> Set
SetoidBinaryMorphism {a} f = ∀ {x y z w : a} -> x ≃ z -> y ≃ w -> f x y ≃ f z w

-- Actually, we don't use these for semirings.
{-
-- The first superclass will be Haskell's Semigroup class.
record SemiGroup (a : Set) : Set₁ where
  field
    overlap {{super1}} : Setoid a
    overlap {{super2}} : Semigroup a
    @0 <>-proper : ∀ {x y z w : a} -> x ≃ z -> y ≃ w -> (x <> y) ≃ (z <> w)
    @0 <>-assoc : ∀ {x y z : a} -> ((x <> y) <> z) ≃ (x <> (y <> z))
open SemiGroup {{...}} public
{-# COMPILE AGDA2HS SemiGroup class #-}

-- Let's choose a name Haskell doesn't use.
record StrictMonoid (a : Set) : Set₁ where
  field
    overlap {{super1}} : Setoid a
    overlap {{super2}} : SemiGroup a
    null : a
    @0 <>-identityˡ : ∀ {x : a} -> (null <> x) ≃ x
    @0 <>-identityʳ : ∀ {x : a} -> (x <> null) ≃ x
open StrictMonoid {{...}} public
{-# COMPILE AGDA2HS StrictMonoid class #-}
-}

record StrongSetoid (a : Set) : Set₁ where
  infix 3 _><_
  field
    overlap {{super}} : Setoid a
    -- For now, we have to erase this to preserve Haskell compatibility.
    @0 _><_ : a -> a -> Set
    @0 ><-irrefl : Irreflexive _><_
    @0 ><-sym : Symmetric _><_
    -- Here, the arguments have to be implicit in order to leave it unerased.
    @0 ><-cotrans : Cotransitive _><_
    @0 ><-tight-apart : ∀ {x y : a} -> (x >< y -> ⊥) ↔ (x ≃ y)
  -- And an alias.
open StrongSetoid {{...}} public
{-# COMPILE AGDA2HS StrongSetoid class #-}

-- A property which we would like a function between two strong setoids to fulfill.
@0 StrongSetoidMorphism : {a b : Set} -> {{StrongSetoid a}} -> {{StrongSetoid b}}
                                   -> (a -> b) -> Set
StrongSetoidMorphism {a} f = ∀ (x y : a) -> f x >< f y -> x >< y
-- We now prove this implies the Setoid version.
@0 strongSetoidMorphismToSetoid : {a b : Set} -> {{stra : StrongSetoid a}} -> {{strb : StrongSetoid b}}
                                   -> (f : a -> b) -> StrongSetoidMorphism {a} {b} {{stra}} {{strb}} f -> SetoidMorphism f
strongSetoidMorphismToSetoid {a} {b} f morphf x y x≃y = fst (><-tight-apart {b}) λ fx><fy → cont x≃y (morphf x y fx><fy)
  where
    cont : x ≃ y -> x >< y -> ⊥
    cont x≃y x><y = snd (><-tight-apart {a}) x≃y x><y

@0 StrongSetoidBinaryMorphism : {a b : Set} -> {{StrongSetoid a}} -> {{StrongSetoid b}}
                                   -> (a -> a -> b) -> Set
StrongSetoidBinaryMorphism {a} f = ∀ (x y z w : a) -> f x y >< f z w -> Either (x >< z) (z >< w)
