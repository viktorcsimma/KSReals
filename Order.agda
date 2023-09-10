-- Classes and predicates related to ordering.
module Order where

open import Haskell.Prim.Either
open import Haskell.Prim using (⊥)
open import Haskell.Prim.Tuple

open import ErasureProduct
open import Relations
open import Setoid
open import Ring

-- A set of which we only know it has a _<_ operator.
-- We need this because we have classes about it that only partially overlap.
record Le (a : Set) : Set₁ where
  infix 4 _≤_
  field
    @0 _≤_ : a -> a -> Set
open Le {{...}} public
{-# COMPILE AGDA2HS Le class #-}

record PartialOrder (a : Set) : Set₁ where
  field
    overlap {{le}} : Le a
    overlap {{setoid}} : Setoid a
    @0 ≤-proper : ∀ (x x' y y' : a) -> x ≃ x' -> y ≃ y'
                                      -> x ≤ y -> x' ≤ y'
open PartialOrder {{...}} public
{-# COMPILE AGDA2HS PartialOrder class #-}

-- An OrderMorphism would simply be a SetoidMorphism on two sets in PartialOrder.

@0 OrderPreserving OrderReflecting OrderEmbedding :
                  {a b : Set} -> {{PartialOrder a}} -> {{PartialOrder b}}
                        -> (a -> b) -> Set
OrderPreserving {a} f = SetoidMorphism f
                          × (∀ (x y : a) -> x ≤ y -> f x ≤ f y)
OrderReflecting {a} f = SetoidMorphism f
                          × (∀ (x y : a) -> f x ≤ f y -> x ≤ y)
OrderEmbedding      f = OrderPreserving f × OrderReflecting f

------------------------
-- Now for strict order.

record Lt (a : Set) : Set₁ where
  infix 4 _<_
  field
    -- We have to erase this one too.
    @0 _<_ : a -> a -> Set
open Lt {{...}} public
{-# COMPILE AGDA2HS Lt class #-}

-- In the Coq standard library, StrictOrder does not include
-- the setoid equality and therefore there is no
-- requirement for properness.
-- But now, we do it here
-- (and therefore, this is rather a cognate of StrictSetoidOrder).
record StrictOrder (a : Set) : Set₁ where
  field
    overlap {{lt}} : Lt a
    overlap {{setoid}} : Setoid a
    @0 <-irrefl : Irreflexive _<_
    @0 <-trans  : Transitive _<_
    @0 <-proper : ∀ {x y z w : a} -> x ≃ z -> y ≃ w -> x < y -> z < w
open StrictOrder {{...}} public
{-# COMPILE AGDA2HS StrictOrder class #-}

record PseudoOrder (a : Set) : Set₁ where
  field
    overlap {{strongSetoid}} : StrongSetoid a
    overlap {{lt}} : Lt a
    @0 <-asym : Asymmetric _<_
    @0 <-cotrans : Cotransitive _<_
    @0 <-total : ∀ (x y : a) -> x >< y ↔ Either (x < y) (y < x)
  @0 _>_ : a -> a -> Set
  x > y = y < x
open PseudoOrder {{...}} public
{-# COMPILE AGDA2HS PseudoOrder class #-}

record TrivialApart (a : Set) : Set₁ where
  field
    overlap {{super}} : StrongSetoid a
    @0 trivialApart : ∀ (x y : a) -> x >< y ↔ (x ≃ y -> ⊥)
open TrivialApart {{...}} public
{-# COMPILE AGDA2HS TrivialApart class #-}

@0 StrictlyOrderPreserving : {a b : Set} -> {{PseudoOrder a}} -> {{PseudoOrder b}}
                                 -> (a -> b) -> Set
StrictlyOrderPreserving {a} f = SetoidMorphism f  -- I didn't quite understand what the difference is between this and StrictSetoidMorphism
                                  × ∀ {x y : a} -> x < y -> f x < f y

@0 StrictOrderEmbedding : {a b : Set} -> {{PseudoOrder a}} -> {{PseudoOrder b}}
                                 -> (a -> b) -> Set
StrictOrderEmbedding {a} f = StrictlyOrderPreserving f
                                  × ∀ {x y : a} -> f x < f y -> x < y

record PseudoRingOrder (a : Set) : Set₁ where
  field
    overlap {{pseudoOrder}} : PseudoOrder a
    overlap {{ring}} : Ring a
    @0 ringMultExt : StrongSetoidBinaryMorphism _*_
    @0 ringPlusPres : ∀ (z : a) -> StrictlyOrderPreserving (z +_)
    @0 ringMultPos : ∀ (x y : a) -> null < x -> null < y -> null < x * y
open PseudoRingOrder {{...}} public
{-# COMPILE AGDA2HS PseudoRingOrder class #-}

record PseudoSemiRingOrder (a : Set) : Set₁ where
  field
    overlap {{pseudoOrder}} : PseudoOrder a
    overlap {{semiring}} : SemiRing a
    -- actually, we never use this for computations
    @0 partialMinus : ∀ x y -> (y < x -> ⊥) -> Σ0 a (λ z -> y ≃ x + z)
    @0 semiRingPlusPres : ∀ (z : a) -> StrictOrderEmbedding (z +_)
    @0 semiRingMultExt : StrongSetoidBinaryMorphism _*_
    @0 ringMultPos : ∀ (x y : a) -> null < x -> null < y -> null < x * y
open PseudoSemiRingOrder {{...}} public
{-# COMPILE AGDA2HS PseudoSemiRingOrder class #-}

record FullPseudoSemiRingOrder (a : Set) : Set₁ where
  field
    overlap {{super}} : PseudoSemiRingOrder a
    overlap {{le}}    : Le a
    @0 leEquivNegLt : ∀ (x y : a) -> x ≤ y ↔ (y < x -> ⊥)
open FullPseudoSemiRingOrder {{...}} public
{-# COMPILE AGDA2HS FullPseudoSemiRingOrder class #-}

