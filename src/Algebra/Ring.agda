-- The SemiRing and Ring classes.
{-# OPTIONS --erasure #-}

module Algebra.Ring where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Algebra.SemiRing
#-}

open import Algebra.Setoid
open import Algebra.SemiRing

-- A ring also has an additive inverse operation.
record Ring (a : Set) : Set₁ where
  field
    overlap {{super}} : SemiRing a
    negate : a -> a
    @0 +-inverseˡ : ∀ (x : a) -> negate x + x ≃ null
    @0 +-inverseʳ : ∀ (x : a) -> x + negate x ≃ null
open Ring {{...}} public
{-# COMPILE AGDA2HS Ring class #-}

infixl 6 _-_
_-_ : {a : Set} -> {{Ring a}} -> a -> a -> a
x - y = x + negate y
-- agda2hs doesn't like it. We'll take a look at that later.
{-# FOREIGN AGDA2HS
(-) :: Ring a => a -> a -> a
a - b = a + negate b
infixl 6 -
#-}

-- A way to convert these to standard Haskell type classes?

-- I don't know whether we can deduce Num from SemiRing;
-- I think not, at least not meaningfully.

-- But even Ring is not enough; since we would also need a decidable ordering
-- which we usually don't have. Hm.
-- And what if we only did that for decidable ordering
-- _and_ then for the completion monad?
