-- Instances for the builtin Nat type.
{-# OPTIONS --erasure #-}

module Implementations.Nat where

{-# FOREIGN AGDA2HS
import qualified Prelude

-- It doesn't import the classes' methods by itself.
-- Maybe we should fix that in agda2hs if the problem is there.
import Algebra.Ring
import Operations.Decidable
import Operations.Pow

-- Sometimes, Nat doesn't get rewritten to Natural.
type Nat = Natural

-- And to bypass suc:
suc :: Natural -> Natural
suc = (1 Prelude.+)
#-}

open import Agda.Builtin.Unit
import Agda.Builtin.Nat
open Agda.Builtin.Nat hiding (_<_; _+_; _*_) -- that's built in for Nat, but is a Boolean operator
open import Agda.Builtin.Equality
open import Haskell.Prim.Tuple
open import Haskell.Prim using (⊥; IsTrue; id; magic)

{-# FOREIGN AGDA2HS {-# LANGUAGE MultiParamTypeClasses #-} #-}

open import Tools.Cheat

open import Tools.PropositionalEquality
open import Algebra.Setoid
open import Operations.Decidable
open import Algebra.Ring
open import Algebra.Order
open import Operations.Pow

@0 _≢0 : Nat -> Set
zero ≢0 = ⊥
_    ≢0 = ⊤

natDiv natMod : (m n : Nat) -> @0 {n ≢0} -> Nat
natDiv m (suc n) = div-helper 0 n m n
-- We'll use `div` instead of this.
natMod m (suc n) = mod-helper 0 n m n
-- And here `mod`.
{-# FOREIGN AGDA2HS
natDiv :: Natural -> Natural -> Natural
natDiv = Prelude.div
natMod :: Natural -> Natural -> Natural
natMod = Prelude.mod
#-}

instance
  setoidNat : Setoid Nat
  setoidNat ._≃_ = _≡_
  setoidNat .≃-refl = refl
  setoidNat .≃-sym refl = refl
  setoidNat .≃-trans refl refl = refl
  {-# COMPILE AGDA2HS setoidNat #-}

  decSetoidNat : DecSetoid Nat
  DecSetoid._≃#_ decSetoidNat = _==_
  DecSetoid.≃#-correct decSetoidNat x y = cheat , cheat

  {-# TERMINATING #-}
  semiRingNat : SemiRing Nat
  -- We have to write this manually;
  -- otherwise it won't recognise that _≃_ is _≡_.
  semiRingNat .super = setoidNat
  semiRingNat ._+_ n m = Agda.Builtin.Nat._+_ n m   -- since the last update, it only compiles when writing the parameters here
  semiRingNat ._*_ n m = Agda.Builtin.Nat._*_ n m
  semiRingNat .+-proper {x} {y} {z} {w} x≡z y≡w = trans (cong (x +_) y≡w)
                                                        (cong (λ t -> t + w) x≡z)
  semiRingNat .+-assoc zero y z = refl
  semiRingNat .+-assoc (suc x) y z = cong suc (+-assoc x y z)
  semiRingNat .*-proper {x} {y} {z} {w} x≡z y≡w = trans (cong (x *_) y≡w) (cong (_* w) x≡z)
  semiRingNat .null = 0
  semiRingNat .one  = 1
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
  DecLe._≤#_ decLeNat n m = n Agda.Builtin.Nat.< (1 + m)
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
  instance Pow Natural Natural where
    n ^ k = go n k 1
      where
        go :: Natural -> Natural -> Natural -> Natural
        go base 0 res = res
        go base exp res = go (base * base) (exp `Prelude.div` 2) (if (Prelude.even exp) then res else res * base)
  #-}

-- This rounds downwards.
halveNat : Nat -> Nat
halveNat zero = zero
halveNat (suc zero) = zero
halveNat (suc (suc n)) = suc (halveNat n)
{-# FOREIGN AGDA2HS
halveNat :: Natural -> Natural
halveNat x = Prelude.div x 2
#-}

-- A function calculating log₂x rounded downwards.
{-# TERMINATING #-}
natLog2Floor : (n : Nat) -> @0 {NonZero n} -> Nat
natLog2Floor (suc zero) = zero
natLog2Floor n@(suc (suc _)) = suc (natLog2Floor (halveNat n))
{-# FOREIGN AGDA2HS
natLog2Floor :: Natural -> Natural
natLog2Floor 0 = Prelude.error "logarithm of 0 would be minus infinity"
natLog2Floor 1 = 0
natLog2Floor n = 1 Prelude.+ (natLog2Floor (Prelude.div n 2))
#-}

@0 natLog2FloorLowerBound : ∀ (x : Nat) {@0 x≢0 : NonZero x} ->
                               2 ^ natLog2Floor x {x≢0} ≤ x
natLog2FloorLowerBound = cheat

@0 natLog2FloorGLB : ∀ (x : Nat) -> {@0 x≢0 : NonZero x} ->
                            (∀ (k : Nat) -> 2 ^ k ≤ x -> k ≤ natLog2Floor x {x≢0})
natLog2FloorGLB = cheat

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

open import Tools.Cheat

instance
  naturalsNat : Naturals Nat
  Naturals.super naturalsNat = semiRingNat
  Naturals.naturalsToSemiRing naturalsNat zero = null
  Naturals.naturalsToSemiRing naturalsNat {{semiRingb}} (suc n) =
                    (semiRingb SemiRing.+ one) (Naturals.naturalsToSemiRing naturalsNat n)
  PreservesOp.setoidMorphism (SemiRingMorphism.preserves-+ (Naturals.isMorphism naturalsNat {{semiRingb}}))
                _ _ refl = ≃-refl {{SemiRing.super semiRingb}}
  PreservesOp.preservesOp (SemiRingMorphism.preserves-+ (Naturals.isMorphism naturalsNat))
                x y = cheat
  PreservesOp.setoidMorphism (SemiRingMorphism.preserves-* (Naturals.isMorphism naturalsNat {{semiRingb}}))
                _ _ refl = ≃-refl {{SemiRing.super semiRingb}}
  PreservesOp.preservesOp (SemiRingMorphism.preserves-* (Naturals.isMorphism naturalsNat))
                x y = cheat
  SemiRingMorphism.preserves-null (Naturals.isMorphism naturalsNat {{semiRingb}}) = ≃-refl {{SemiRing.super semiRingb}}
  SemiRingMorphism.preserves-one (Naturals.isMorphism naturalsNat {{semiRingb}}) = +-identityʳ {{semiRingb}} one
  Naturals.isUnique naturalsNat {{semiRingb}} {f = f} record { preserves-+ = preserves-+ ; preserves-* = preserves-* ; preserves-null = preserves-null ; preserves-one = preserves-one } zero
                    = ≃-sym {{super semiRingb}} preserves-null
  Naturals.isUnique naturalsNat {f = f} record { preserves-+ = preserves-+ ; preserves-* = preserves-* ; preserves-null = preserves-null ; preserves-one = preserves-one } (suc x) = cheat
  -- {-# COMPILE AGDA2HS naturalsNat #-}
  -- For now, we circumvent the `suc` problem by saying:
  {-# FOREIGN AGDA2HS
  instance Naturals Natural where
    naturalsToSemiRing 0 = null
    naturalsToSemiRing n = one + naturalsToSemiRing (n Prelude.- 1)
  #-}
