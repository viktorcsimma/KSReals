module KSReals where

open import Haskell.Prim.Monoid using (Semigroup; _<>_)
open import Haskell.Prim using (⊥)
open import Haskell.Prim.Tuple
open import Haskell.Prim.Either

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit

record Setoid (a : Set) : Set₁ where
  infix 3 _≃_
  field
    @0 _≃_ : a -> a -> Set
    @0 ≃-refl : ∀ {x : a} -> x ≃ x
    @0 ≃-sym  : ∀ {x y : a} -> x ≃ y -> y ≃ x
    @0 ≃-trans : ∀ {x y z : a} -> x ≃ y -> y ≃ z -> x ≃ z
open Setoid {{...}} public
{-# COMPILE AGDA2HS Setoid class #-}

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
    @0 +-proper : ∀ {x y z w : a} -> x ≃ z -> y ≃ w -> (x + y) ≃ (z + w)
    @0 +-assoc : ∀ {x y z : a} -> (x + y) + z ≃ x + (y + z)
    @0 *-proper : ∀ {x y z w : a} -> x ≃ z -> y ≃ w -> (x * y) ≃ (z * w)
    @0 *-assoc : ∀ {x y z : a} -> (x * y) * z ≃ x * (y * z)

    -- StrictMonoid
    null one : a
    @0 +-identityˡ : ∀ {x : a} -> (null + x) ≃ x
    @0 +-identityʳ : ∀ {x : a} -> (x + null) ≃ x
    @0 *-identityˡ : ∀ {x : a} -> (one  * x) ≃ x
    @0 *-identityʳ : ∀ {x : a} -> (x *  one) ≃ x

    -- the new ones
    @0 +-comm : ∀ {x y : a} -> (x + y) ≃ (y + x)
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

-- Fractions of semiring elements.
-- I'm not quite sure how to express ≄ here.
-- But I don't see any options other than -> ⊥.
data Frac (a : Set) {{semiring : SemiRing a}} : Set where
  MkFrac : (num : a) (den : a) -> @0 ((den ≃ null) -> ⊥) -> Frac a
{-# COMPILE AGDA2HS Frac #-}

-- Logical equivalence.
infix 2 _↔_
_↔_ : Set -> Set -> Set
a ↔ b = (a -> b) × (b -> a)
{-# COMPILE AGDA2HS _↔_ #-}

-- Some useful shortenings for later.
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

-- Whether a function between two setoids is proper.
@0 setoidMorphism : {a b : Set} -> {{Setoid a}} -> {{Setoid b}}
                                   -> (a -> b) -> Set
setoidMorphism {a} f = ∀ (x y : a) -> x ≃ y -> f x ≃ f y

-- A property which we would like a function between two strong setoids to fulfill.
@0 strongSetoidMorphism : {a b : Set} -> {{StrongSetoid a}} -> {{StrongSetoid b}}
                                   -> (a -> b) -> Set
strongSetoidMorphism {a} f = ∀ (x y : a) -> f x >< f y -> x >< y

-- We now prove the second implies the first.
@0 strongSetoidMorphismToSetoid : {a b : Set} -> {{stra : StrongSetoid a}} -> {{strb : StrongSetoid b}}
                                   -> (f : a -> b) -> strongSetoidMorphism {a} {b} {{stra}} {{strb}} f -> setoidMorphism f
strongSetoidMorphismToSetoid f morphf x y x≃y = fst ><-tight-apart λ fx><fy → cont x≃y (morphf x y fx><fy) 
  where
    cont : x ≃ y -> x >< y -> ⊥
    cont x≃y x><y = snd ><-tight-apart x≃y x><y

-- For binary operators on a.
@0 strongSetoidBinaryMorphism : {a b : Set} -> {{StrongSetoid a}} -> {{StrongSetoid b}}
                                   -> (a -> a -> b) -> Set
strongSetoidBinaryMorphism {a} f = ∀ (x y z w : a) -> f x y >< f z w -> Either (x >< z) (z >< w) 

record Field (a : Set) : Set₁ where
  field
    overlap {{ring}} : Ring a
    overlap {{strongSetoid}} : StrongSetoid a
    -- binaryMorphism _+_
    -- binaryMorphism _*_

    -- nullNeqOne : null >< one

    {-
    recip : (x : a) -> x >< null -> a
    -- I don't know yet how we could use setoidMorphism; the x><0 argument makes this hard.
    @0 recipProper : ∀ {x y : a} (x><null : x >< null) (y><null : y >< null)
                               -> x ≃ y -> recip x x><null ≃ recip y y><null
    @0 *-inverseˡ : ∀ {x : a} (x><null : x >< null) -> recip x x><null * x ≃ one
    @0 *-inverseʳ : ∀ {x : a} (x><null : x >< null) -> x * recip x x><null ≃ one
    -}
open Field {{...}} public
{-# COMPILE AGDA2HS Field class #-}

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
    
{-
@0 StrictlyOrderPreserving : {a b : Set} -> {{PseudoOrder a}} -> {{PseudoOrder b}}
                                 -> (a -> b) -> Set
StrictlyOrderPreserving {a} f = ∀ (x y : a) -> 
-}
@0 _≢0 : Nat -> Set
zero ≢0 = ⊥
_    ≢0 = ⊤

data Rational : Set where
  MkRational : (numerator : Int) (denominator : Nat) -> @0 {denominator ≢0} -> Rational

record AppRationals (aq : Set) : Set₁ where
  field
    overlap {{ring}} : Ring aq
    overlap {{tApart}} : TrivialApart aq

    toRational : aq -> Rational
    
