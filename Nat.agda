-- Instances for the builtin Nat type.
module Nat where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_<_) -- that's built in for Nat, but is a Boolean operator
open import Agda.Builtin.Equality
open import Haskell.Prim.Tuple
open import Haskell.Prim using (⊥; IsTrue; id; magic)

{-# FOREIGN AGDA2HS {-# LANGUAGE MultiParamTypeClasses #-} #-}

open import Cheat

open import PropositionalEquality
open import Setoid
open import Decidable
import Ring
open Ring hiding (_+_; _*_) -- here we use the Nat ones by default
open import Order
open import Operations

@0 _≢0 : Nat -> Set
zero ≢0 = ⊥
_    ≢0 = ⊤

infixl 7 _natDiv_
_natDiv_ : (m n : Nat) -> @0 {n ≢0} -> Nat
m natDiv (suc n) = div-helper 0 n m n
-- We'll use `div` instead of this.

instance
  setoidNat : Setoid Nat
  setoidNat ._≃_ = _≡_
  setoidNat .≃-refl = refl
  setoidNat .≃-sym refl = refl
  setoidNat .≃-trans refl refl = refl

  decSetoidNat : DecSetoid Nat
  DecSetoid._≃#_ decSetoidNat = _==_
  DecSetoid.≃#-correct decSetoidNat x y = cheat , cheat

  {-# TERMINATING #-}
  semiRingNat : SemiRing Nat
  -- We have to write this manually;
  -- otherwise it won't recognise that _≃_ is _≡_.
  semiRingNat .super = setoidNat
  SemiRing._+_ semiRingNat = _+_
  SemiRing._*_ semiRingNat = _*_
  semiRingNat .+-proper {x} {y} {z} {w} x≡z y≡w = trans (cong (x +_) y≡w) (cong (_+ w) x≡z)
  semiRingNat .+-assoc zero y z = refl
  semiRingNat .+-assoc (suc x) y z = cong suc (+-assoc x y z)
  semiRingNat .*-proper {x} {y} {z} {w} x≡z y≡w = trans (cong (x *_) y≡w) (cong (_* w) x≡z)
  semiRingNat .null = zero
  semiRingNat .one = suc zero
  semiRingNat .NonZero = _≢0
  semiRingNat .NonZeroCorrect zero = magic , λ f -> f refl
  semiRingNat .NonZeroCorrect (suc n) = (λ _ ()) , λ _ -> tt
  semiRingNat .NonZeroOne = tt
  semiRingNat .+-identityˡ _ = refl
  semiRingNat .+-identityʳ zero = refl
  semiRingNat .+-identityʳ (suc x) = cong suc (+-identityʳ x)
  semiRingNat .*-identityˡ x = +-identityʳ x
  semiRingNat .*-identityʳ zero = refl
  semiRingNat .*-identityʳ (suc x) = cong suc (*-identityʳ x)
  semiRingNat .+-comm zero y = sym (+-identityʳ y)
  semiRingNat .+-comm (suc x) y = trans (cong suc (+-comm x y))
                                        (sym (+-suc y x))
    where
    @0 +-suc : ∀ (x y : Nat) -> x + suc y ≡ suc (x + y)
    +-suc zero y = refl
    +-suc (suc x) y = cong suc (+-suc x y)
  semiRingNat .*-comm zero zero = refl
  semiRingNat .*-comm zero (suc y) = *-comm zero y
  semiRingNat .*-comm (suc x) y = trans (cong (y +_) (*-comm x y))
                                        (sym (*-suc y x))
    where
    -- see the standard library
    @0 *-suc : ∀ (x y : Nat) -> x * suc y ≡ x + x * y
    *-suc    zero y = refl
    *-suc (suc x) y =  trans (cong (suc y +_) (*-suc x y))
                      (trans (cong suc (sym (+-assoc y x (x * y))))
                      (trans (cong (λ t → suc (t + x * y)) (+-comm y x))
                             (cong suc (+-assoc x y (x * y)))))
  semiRingNat .*-nullˡ _ = refl
  semiRingNat .*-nullʳ zero = refl
  semiRingNat .*-nullʳ (suc x) = *-nullʳ x
  semiRingNat .*-distribʳ-+ x zero z = refl
  -- x + (y + z) * x = x + (y * x + z * x) = x + y * x + z * x
  semiRingNat .*-distribʳ-+ x (suc y) z = trans (cong (x +_) (*-distribʳ-+ x y z))
                                                (sym (+-assoc x (y * x) (z * x)))
  semiRingNat .*-distribˡ-+ x zero z = cong (_+ (x * z)) (sym (*-nullʳ x))
  semiRingNat .*-distribˡ-+ zero (suc y) z = refl
  -- y + z + x * (suc y + z) = y + z + (x * suc y + x * z) = y + z + x * suc y + x * z =
  --     = y + (z + x * suc y) + x * z = y + (x * suc y + z) + x * z = y + x * suc y + z + x * z = y + x * suc y + z + x * z
  semiRingNat .*-distribˡ-+ (suc x) (suc y) z = cong suc (trans (cong ((y + z) +_) (*-distribˡ-+ x (suc y) z))
                                                         (trans (sym (+-assoc (y + z) (x * suc y) (x * z)))
                                                         (trans (cong (_+ (x * z)) (+-assoc y z (x * suc y)))
                                                         (trans (cong (λ t -> y + t + x * z) (+-comm z (x * suc y)))
                                                         (trans (cong (_+ (x * z)) (sym (+-assoc y (x * suc y) z)))
                                                                (+-assoc (y + x * suc y) z (x * z)))))))
  semiRingNat .*-assoc zero y z = refl
  -- (y + x * y) * z = y * z + x * y * z = y * z + x * (y * z)
  semiRingNat .*-assoc (suc x) y z = trans (cheatHere x y z)
                                           (cong ((y * z) +_) (*-assoc x y z))
    where
    -- This is only accepted because of the TERMINATING pragma. I don't know why.
    @0 cheatHere : ∀ (x y z : Nat) -> (y + x * y) * z ≡ y * z + x * y * z
    cheatHere x y z = *-distribʳ-+ z y (x * y)
  {-# COMPILE AGDA2HS semiRingNat #-}

  -- Order-related instances
  leNat : Le Nat
  Le._≤_ leNat n m = IsTrue (n Agda.Builtin.Nat.< (suc m))
  {-# COMPILE AGDA2HS leNat #-}

  decLeNat : DecLe Nat
  DecLe.le decLeNat = leNat
  DecLe._≤#_ decLeNat n m = n Agda.Builtin.Nat.< (suc m)
  DecLe.≤#-correct decLeNat n m = id , id
  {-# COMPILE AGDA2HS decLeNat #-}

  partialOrderNat : PartialOrder Nat
  PartialOrder.le partialOrderNat = leNat
  PartialOrder.setoid partialOrderNat = setoidNat
  PartialOrder.≤-proper partialOrderNat _ _ _ _ refl refl P = P
  {-# COMPILE AGDA2HS partialOrderNat #-}

  ltNat : Lt Nat
  Lt._<_ ltNat n m = IsTrue (n Agda.Builtin.Nat.< m)
  {-# COMPILE AGDA2HS ltNat #-}

  decLtNat : DecLt Nat
  DecLt.lt decLtNat = ltNat
  DecLt._<#_ decLtNat = Agda.Builtin.Nat._<_
  DecLt.<#-correct decLtNat n m = id , id
  {-# COMPILE AGDA2HS decLtNat #-}

  natPowNat : Pow Nat Nat
  (natPowNat Pow.^ n) zero = suc zero
  (natPowNat Pow.^ n) (suc k) = n * n ^ k
  Pow.powProper natPowNat refl refl = refl
  Pow.powNull natPowNat = λ _ -> refl
  Pow.powSuc natPowNat = λ _ _ -> refl
  {-# FOREIGN AGDA2HS
  -- We'll change this to a more efficient implementation.
  instance NatPow Natural Natural where
    n ^ k = go n k 1
      where
        go :: Natural -> Natural -> Natural -> Natural
        go base 0 res = res
        go base exp res = go (base * base) (exp `div` 2) (if (even exp) then res else res * base)
  #-}
  
  shiftLNat : ShiftL Nat Nat
  ShiftL.semiringa shiftLNat = semiRingNat
  ShiftL.semiringb shiftLNat = semiRingNat
  ShiftL.shiftl shiftLNat n zero = n
  ShiftL.shiftl shiftLNat n (suc k) = 2 * shiftl n k
  ShiftL.shiftlProper shiftLNat _ _ _ _ refl refl = refl
  ShiftL.shiftlNull shiftLNat _ = refl
  ShiftL.shiftlSuc shiftLNat x y = cheat
  -- {-# COMPILE AGDA2HS shiftLNat #-}
  -- For there is a `suc` constructor:
  {-# FOREIGN AGDA2HS
  instance ShiftL Nat Nat where
    shiftl n 0 = n
    shiftl n k = 2 * shiftl n (k - 1)
  #-}

-- An initial object of a category C is an object I in C such that for every object X in C, there exists precisely one morphism I → X.
-- This morphism is called the initial arrow.
-- But I think we cannot really generalise this while preserving agda2hs compatibility.
-- The structure-preserving nature of a morphism makes this even harder;
-- since we cannot generally now what the structure is in a given category.

-- We define an abstract type class which enables us to change the representation on demand.
record Naturals (a : Set) : Set₁ where
  field
    overlap {{super}} : SemiRing a
    -- We make this a bit less general, by requiring b to be a SemiRing too.
    naturalsToSemiRing : ∀ {b : Set} -> {{SemiRing b}} -> a -> b
    @0 isMorphism : ∀ {b : Set} -> {{semiRingb : SemiRing b}} ->
                                       SemiRingMorphism {a} {b} naturalsToSemiRing
    @0 isUnique : ∀ {b : Set} -> {{semiRingb : SemiRing b}} ->
                     ∀ {f : a -> b} -> SemiRingMorphism {a} {b} f ->
                     (∀ (x : a) -> naturalsToSemiRing x ≃ f x)          -- every function which can do the same is equivalent
open Naturals {{...}} public
-- {-# COMPILE AGDA2HS Naturals class #-}
-- This should work, but it doesn't...
-- We should fix this in agda2hs. But for now:
{-# FOREIGN AGDA2HS
class SemiRing a => Naturals a where
  naturalsToSemiRing :: SemiRing b => a -> b
#-}

open import Cheat

instance
  naturalsNat : Naturals Nat
  Naturals.super naturalsNat = semiRingNat
  Naturals.naturalsToSemiRing naturalsNat zero = null
  Naturals.naturalsToSemiRing naturalsNat {{semiRingb}} (suc n) =
                    (semiRingb SemiRing.+ one) (Naturals.naturalsToSemiRing naturalsNat n)
  PreservesOp.setoidMorphism (SemiRingMorphism.preserves-+ (Naturals.isMorphism naturalsNat))
                _ _ refl = ≃-refl
  PreservesOp.preservesOp (SemiRingMorphism.preserves-+ (Naturals.isMorphism naturalsNat))
                x y = cheat
  PreservesOp.setoidMorphism (SemiRingMorphism.preserves-* (Naturals.isMorphism naturalsNat))
                _ _ refl = ≃-refl
  PreservesOp.preservesOp (SemiRingMorphism.preserves-* (Naturals.isMorphism naturalsNat))
                x y = cheat
  SemiRingMorphism.preserves-null (Naturals.isMorphism naturalsNat) = ≃-refl
  SemiRingMorphism.preserves-one (Naturals.isMorphism naturalsNat) = +-identityʳ one
  Naturals.isUnique naturalsNat {f = f} record { preserves-+ = preserves-+ ; preserves-* = preserves-* ; preserves-null = preserves-null ; preserves-one = preserves-one } zero = ≃-sym preserves-null
  Naturals.isUnique naturalsNat {f = f} record { preserves-+ = preserves-+ ; preserves-* = preserves-* ; preserves-null = preserves-null ; preserves-one = preserves-one } (suc x) = cheat
  -- {-# COMPILE AGDA2HS naturalsNat #-}
  -- For now, we circumvent the `suc` problem by saying:
  {-# FOREIGN AGDA2HS
  instance Naturals Natural where
    naturalsToSemiRing 0 = null
    naturalsToSemiRing n = one + naturalsToSemiRing (n - 1)
  #-}
