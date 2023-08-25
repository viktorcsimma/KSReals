-- The SemiRing and Ring classes.
module Ring where

open import Setoid

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
    @0 +-identityˡ : ∀ {x : a} -> (null + x) ≃ x
    @0 +-identityʳ : ∀ {x : a} -> (x + null) ≃ x
    @0 *-identityˡ : ∀ {x : a} -> (one  * x) ≃ x
    @0 *-identityʳ : ∀ {x : a} -> (x *  one) ≃ x

    -- the new ones
    @0 +-comm : Commutative _+_
    @0 *-nullˡ : ∀ {x : a} -> (null * x) ≃ null
    @0 *-nullʳ : ∀ {x : a} -> (x * null) ≃ null
    @0 *-+-distribˡ : ∀ {x y z : a} -> (x * (y + z)) ≃ ((x * y) + (x * z))
    @0 *-+-distribʳ : ∀ {x y z : a} -> ((x + y) * z) ≃ ((x * z) + (y * z))
open SemiRing {{...}} public
{-# COMPILE AGDA2HS SemiRing class #-}

-- A ring also has an additive inverse operation.
record Ring (a : Set) : Set₁ where
  field
    overlap {{super}} : SemiRing a
    negate : a -> a
    @0 +-inverseˡ : ∀ {x : a} -> negate x + x ≃ null
    @0 +-inverseʳ : ∀ {x : a} -> x + negate x ≃ null
open Ring {{...}} public
{-# COMPILE AGDA2HS Ring class #-}
