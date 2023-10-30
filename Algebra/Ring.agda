-- The SemiRing and Ring classes.
{-# OPTIONS --erasure #-}

module Algebra.Ring where

{-# FOREIGN AGDA2HS
import qualified Prelude
#-}

open import Agda.Builtin.Unit
open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Int using (pos; negsuc)
open import Haskell.Prim using (⊥)

open import Tools.Relations
open import Algebra.Setoid

-- The trick is that
-- we list the criteria directly for _+_ and _*_
-- (actually, we won't use most of the above classes).
-- This will be quite ugly, but will save us from a lot of problems later.
record SemiRing (a : Set) : Set₁ where
  infixl 6 _+_
  infixl 7 _*_
  field
    overlap {{super}} : Setoid a
    _+_ _*_ : a -> a -> a

    -- SemiGroup
    @0 +-proper : SetoidBinaryMorphism _+_
    @0 +-assoc : Associative _+_
    @0 *-proper : SetoidBinaryMorphism _*_
    @0 *-assoc : Associative _*_

    -- StrictMonoid
    null one : a

    -- A simple predicate for a nonzero element.
    -- Of course, this could be defined as (x ≃ null) -> ⊥,
    -- but often there are prettier solutions with pattern matching.
    @0 NonZero : a -> Set
    @0 NonZeroCorrect : ∀ (x : a) -> NonZero x ↔ (x ≃ null -> ⊥)

    -- Actually, this doesn't belong to the definition of a semiring
    -- in a strict sense. But sometimes we need this,
    -- and semirings without this axiom aren't very useful anyway.
    @0 NonZeroOne : NonZero one

    @0 +-identityˡ : ∀ (x : a) -> (null + x) ≃ x
    @0 +-identityʳ : ∀ (x : a) -> (x + null) ≃ x
    @0 *-identityˡ : ∀ (x : a) -> (one  * x) ≃ x
    @0 *-identityʳ : ∀ (x : a) -> (x *  one) ≃ x

    -- the new ones (here, we expect _*_ to be commutative too)
    @0 +-comm : Commutative _+_
    @0 *-comm : Commutative _*_
    @0 *-nullˡ : ∀ (x : a) -> (null * x) ≃ null
    @0 *-nullʳ : ∀ (x : a) -> (x * null) ≃ null
    @0 *-distribˡ-+ : ∀ (x y z : a) -> (x * (y + z)) ≃ ((x * y) + (x * z))
    @0 *-distribʳ-+ : ∀ (x y z : a) -> ((y + z) * x) ≃ ((y * x) + (z * x))
open SemiRing {{...}} public
{-# COMPILE AGDA2HS SemiRing class #-}

-- For the next one.
-- Takes the role of SemiGroup_Morphism.
record PreservesOp {a b : Set} {{setoida : Setoid a}} {{setoidb : Setoid b}}
                         (f : a -> b)
                         (op1 : a -> a -> a)
                         (op2 : b -> b -> b)
                         : Set where
    field
      @0 setoidMorphism : SetoidMorphism f
      @0 preservesOp : ∀ (x y : a) -> f (op1 x y) ≃ op2 (f x) (f y)
open PreservesOp public
-- We won't compile this.

-- Now the one that we want.
record SemiRingMorphism {a b : Set} {{semiRinga : SemiRing a}} {{semiRingb : SemiRing b}}
                        (f : a -> b)
                        : Set where
    field
      @0 preserves-+ : PreservesOp {a} {b} f _+_ _+_
      @0 preserves-* : PreservesOp {a} {b} f _*_ _*_
      @0 preserves-null : f null ≃ null
      @0 preserves-one  : f one ≃ one
-- We won't compile this either.


-- A ring also has an additive inverse operation.
record Ring (a : Set) : Set₁ where
  field
    overlap {{super}} : SemiRing a
    negate : a -> a
    @0 +-inverseˡ : ∀ (x : a) -> negate x + x ≃ null
    @0 +-inverseʳ : ∀ (x : a) -> x + negate x ≃ null
open Ring {{...}} public
{-# COMPILE AGDA2HS Ring class #-}

_-_ : {a : Set} -> {{Ring a}} -> a -> a -> a
x - y = x + negate y
-- agda2hs doesn't like it. We'll take a look at that later.
{-# FOREIGN AGDA2HS
(-) :: Ring a => a -> a -> a
a - b = a + negate b
#-}

-- A way to convert these to standard Haskell type classes?

-- I don't know whether we can deduce Num from SemiRing;
-- I think not, at least not meaningfully.

-- But even Ring is not enough; since we would also need a decidable ordering
-- which we usually don't have. Hm.
-- And what if we only did that for decidable ordering
-- _and_ then for the completion monad?
