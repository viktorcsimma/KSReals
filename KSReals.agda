module KSReals where

open import Haskell.Prim using (⊥)

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit

open import Relations
open import Setoid
open import Ring
open import Order

-- Fractions of semiring elements.
-- I'm not quite sure how to express ≄ here.
-- But I don't see any options other than -> ⊥.
data Frac (a : Set) {{semiring : SemiRing a}} : Set where
  MkFrac : (num : a) (den : a) -> @0 ((den ≃ null) -> ⊥) -> Frac a
{-# COMPILE AGDA2HS Frac #-}

@0 _≢0 : Nat -> Set
zero ≢0 = ⊥
_    ≢0 = ⊤

Rational : Set
Rational = Frac Int

record AppRationals (aq : Set) : Set₁ where
  field
    overlap {{ring}} : Ring aq
    overlap {{tApart}} : TrivialApart aq
    overlap {{pseudoOrder}} : PseudoOrder aq

    toRational : aq -> Rational
    -- OrderEmbedding toRational
    -- @0 toRational-strictOrderEmbedding : StrictOrderEmbedding toRational
    
