-- Some properties of _≡_ we don't want to import from the standard library.
-- Copied from Relation/Binary/PropositionalEquality/Core.agda.
module Tools.PropositionalEquality where

open import Agda.Builtin.Equality

open import Tools.Relations

@0 cong : ∀ {i} {a b : Set i} (f : a -> b) {x y : a} → x ≡ y → f x ≡ f y
cong f refl = refl 

@0 sym : ∀ {i} {a : Set i} -> Symmetric {i} {a} _≡_
sym refl = refl

@0 trans : ∀ {i} {a : Set i} -> Transitive {i} {a} _≡_
trans refl eq = eq

@0 subst : ∀ {i} {a : Set i} {x y : a} (P : a → Set)
                  -> x ≡ y -> P x -> P y
subst P refl Px = Px
