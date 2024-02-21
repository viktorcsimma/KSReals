-- Instances for the builtin Int type.
{-# OPTIONS --erasure #-}

module Implementation.Int where

{-# FOREIGN AGDA2HS
{-# LANGUAGE MultiParamTypeClasses #-}
import qualified Prelude
import Prelude (Integer, Integral)
import Numeric.Natural
import Data.Bits (shift)

-- It doesn't import the classes' methods by itself.
-- Maybe we should fix that in agda2hs if the problem is there.

import Operator.Decidable
import Operator.Abs
import Operator.Pow
import Algebra.SemiRing
import Algebra.Ring
import Implementation.Nat

-- Sometimes, Int doesn't get rewritten to Integer.
type Int = Integer

-- And to bypass the case where "pos" or "negsuc" remains in the code:
pos :: Natural -> Integer
pos = Prelude.fromIntegral
negsuc :: Natural -> Integer
negsuc x = Prelude.fromIntegral x - 1
#-}

open import Tool.Cheat

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
import Agda.Builtin.Nat
open Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.Equality
open import Haskell.Prim using (⊥; _∘_; magic; ltNat; addNat; id; itsTrue)
open import Haskell.Prim.Tuple
open import Haskell.Prim.Integer using (IsNonNegativeInteger)

open import Tool.PropositionalEquality
open import Algebra.Setoid
open import Operator.Decidable
open import Algebra.SemiRing
open import Algebra.Ring
open import Implementation.Nat
open import Algebra.Order
open import Operator.Abs
open import Operator.Pow

-- Here, the operators are not pre-defined;
-- so we have to copy them from the standard library.

private
  intNegate : Int -> Int
  intNegate (pos zero) = pos zero
  intNegate (pos (suc n)) = negsuc n
  intNegate (negsuc n) = pos (suc n)

  -- From the standard library:
  -- Subtraction of natural numbers.
  -- We define it using _<ᵇ_ and _∸_ rather than inductively so that it
  -- is backed by builtin operations. This makes it much faster.

  natSub : Nat -> Nat -> Int
  natSub m n with m Agda.Builtin.Nat.< n
  ... | true  = intNegate (pos (n Agda.Builtin.Nat.- m))
  ... | false = pos (m Agda.Builtin.Nat.- n)

  {-
  The inductive version:
  natSub' : Nat -> Nat -> Int
  natSub' m zero = pos m
  natSub' zero (suc n) = negsuc n
  natSub' (suc m) (suc n) = natSub' m n
  -}

  @0 natSubSameIsZero : ∀ (x : Nat) -> natSub x x ≡ pos zero
  natSubSameIsZero zero = refl
  natSubSameIsZero (suc x) with Haskell.Prim.ltNat x x in eq
  ... | true = magic (subst prop (trans (sym eq) (x<xIsFalse x)) tt)
    where
    @0 prop : Bool -> Set
    prop true = ⊤
    prop false = ⊥
    @0 x<xIsFalse : ∀ (x : Nat) -> Haskell.Prim.ltNat x x ≡ false
    x<xIsFalse zero = refl
    x<xIsFalse (suc x) = x<xIsFalse x
  ... | false = cong pos (xMonusNatxIsZero x)
    where
    @0 xMonusNatxIsZero : ∀ (x : Nat) -> Haskell.Prim.monusNat x x ≡ 0
    xMonusNatxIsZero zero = refl
    xMonusNatxIsZero (suc x) = xMonusNatxIsZero x

  intPlus : Int -> Int -> Int
  intPlus (pos x) (pos y) = pos (x Agda.Builtin.Nat.+ y)
  intPlus (pos x) (negsuc y) = natSub x (suc y)
  intPlus (negsuc x) (pos y) = natSub y (suc x)
  intPlus (negsuc x) (negsuc y) = negsuc (suc (x Agda.Builtin.Nat.+ y))
  -- We won't compile this. Instead, we'll use Haskell's builtin operators.
  {-# FOREIGN AGDA2HS
  intPlus :: Integer -> Integer -> Integer
  intPlus a b = a Prelude.+ b       -- for some reason, GHC only accepts it this way
  #-}

  -- Now multiplication. We won't compile this either.
  intTimes : Int -> Int -> Int
  intTimes (pos n) (pos n₁) = pos (n Agda.Builtin.Nat.* n₁)
  intTimes (pos n) (negsuc n₁) = intNegate (pos (n Agda.Builtin.Nat.* suc n₁))
  intTimes (negsuc n) (pos n₁) = intNegate (pos (suc n Agda.Builtin.Nat.* n₁))
  intTimes (negsuc n) (negsuc n₁) = pos (suc n Agda.Builtin.Nat.* suc n₁)
  {-# FOREIGN AGDA2HS
  intTimes :: Integer -> Integer -> Integer
  intTimes a b = a Prelude.* b
  #-}

  @0 _≢+0 : Int -> Set
  pos zero ≢+0 = ⊥
  _        ≢+0 = ⊤

-- 0.5 will be rounded to 0;
-- -0.5 to -1.
-- So like in Python.
-- This will be used in the Shift instance;
-- so this has to be public.
halveInt : Int -> Int
halveInt (pos n) = pos (halveNat n)
halveInt (negsuc n) = negsuc (halveNat n)

-- Now these have to be public.
intQuot intRem : (x y : Int) -> @0 (y ≢+0) -> Int
intQuot (pos m) (pos (suc n)) _ = pos (natDiv m (suc n) tt)
intQuot (pos m) (negsuc n) _ = intNegate (pos (natDiv m (suc n) tt))
intQuot (negsuc m) (pos (suc n)) _ = intNegate (pos (natDiv (suc m) (suc n) tt))
intQuot (negsuc m) (negsuc n) _ = pos (natDiv (suc m) (suc n) tt)
intRem x y y≢+0 = intPlus x (intNegate (intTimes y (intQuot x y y≢+0)))
-- And we will use `quot` in Haskell (this rounds towards zero).
-- (`div` would be uglier now.)
{-# FOREIGN AGDA2HS
intQuot :: Integer -> Integer -> Integer
intQuot = Prelude.quot
intRem  :: Integer -> Integer -> Integer
intRem  = Prelude.rem
#-}

natAbs : Int -> Nat
natAbs (pos n) = n
natAbs (negsuc n) = suc n
{-# FOREIGN AGDA2HS
natAbs :: Integer -> Natural
natAbs = Prelude.fromInteger Prelude.. Prelude.abs
#-}

instance
  setoidInt : Setoid Int
  setoidInt ._≃_ = _≡_
  setoidInt .≃-refl = refl
  setoidInt .≃-sym refl = refl
  setoidInt .≃-trans refl refl = refl
  {-# COMPILE AGDA2HS setoidInt #-}

  decSetoidInt : DecSetoid Int
  DecSetoid.setoid decSetoidInt = setoidInt
  (decSetoidInt DecSetoid.≃# pos n) (pos n₁)       = n Agda.Builtin.Nat.== n₁
  (decSetoidInt DecSetoid.≃# negsuc n) (negsuc n₁) = n Agda.Builtin.Nat.== n₁
  (decSetoidInt DecSetoid.≃# _) _                  = false
  DecSetoid.≃#-correct decSetoidInt (pos n) (pos n₁) = cheat
  DecSetoid.≃#-correct decSetoidInt (pos n) (negsuc n₁) = (λ ()) , λ ()
  DecSetoid.≃#-correct decSetoidInt (negsuc n) (pos n₁) = (λ ()) , λ ()
  DecSetoid.≃#-correct decSetoidInt (negsuc n) (negsuc n₁) = cheat
  {-# FOREIGN AGDA2HS
  instance DecSetoid Integer where
    a ≃# b = a Prelude.== b  -- For some reason, GHC only accepts it in this form.
  #-}

  strongSetoidInt : StrongSetoid Int
  StrongSetoid.super strongSetoidInt = setoidInt
  StrongSetoid._><_ strongSetoidInt x y = x ≡ y -> ⊥
  StrongSetoid.><-irrefl strongSetoidInt eq neq = neq eq
  StrongSetoid.><-sym strongSetoidInt neq refl = neq refl
  StrongSetoid.><-cotrans strongSetoidInt neqxy z = cheat  -- I think _≡_ is decidable; isn't it?
  StrongSetoid.><-tight-apart strongSetoidInt = cheat , λ eq neq -> neq eq
  {-# COMPILE AGDA2HS strongSetoidInt #-}

  semiRingInt : SemiRing Int
  SemiRing.super semiRingInt = setoidInt
  SemiRing._+_ semiRingInt = intPlus
  SemiRing._*_ semiRingInt = intTimes
  SemiRing.+-proper semiRingInt refl refl = refl
  SemiRing.+-assoc semiRingInt x y z = cheat
  SemiRing.*-proper semiRingInt refl refl = refl
  SemiRing.*-assoc semiRingInt x y z = cheat
  SemiRing.null semiRingInt = pos 0
  SemiRing.one semiRingInt  = pos 1
  SemiRing.NonZero semiRingInt = _≢+0
  SemiRing.NonZeroCorrect semiRingInt (pos zero) = magic , λ f -> f refl
  SemiRing.NonZeroCorrect semiRingInt (pos (suc n)) = (λ _ ()) , λ _ -> tt
  SemiRing.NonZeroCorrect semiRingInt (negsuc n) = (λ _ ()) , λ _ -> tt
  SemiRing.NonZeroOne semiRingInt = tt
  SemiRing.+-identityˡ semiRingInt (pos n) = refl
  SemiRing.+-identityˡ semiRingInt (negsuc n) = refl
  SemiRing.+-identityʳ semiRingInt (pos n) = cong pos (+-identityʳ n)
  SemiRing.+-identityʳ semiRingInt (negsuc n) = refl
  SemiRing.*-identityˡ semiRingInt (pos n) = cong pos (+-identityʳ n)
  SemiRing.*-identityˡ semiRingInt (negsuc n) = cong negsuc (+-identityʳ n)
  SemiRing.*-identityʳ semiRingInt (pos n) = cong pos (*-identityʳ n)
  SemiRing.*-identityʳ semiRingInt (negsuc n) = cong negsuc (*-identityʳ n)
  SemiRing.+-comm semiRingInt (pos n) (pos n₁) = cong pos (+-comm n n₁)
  SemiRing.+-comm semiRingInt (pos n) (negsuc n₁) = refl
  SemiRing.+-comm semiRingInt (negsuc n) (pos n₁) = refl
  SemiRing.+-comm semiRingInt (negsuc n) (negsuc n₁) = cong (negsuc ∘ suc) (+-comm n n₁)
  SemiRing.*-comm semiRingInt = cheat
  SemiRing.*-nullˡ semiRingInt (pos n) = refl
  SemiRing.*-nullˡ semiRingInt (negsuc n) = refl
  SemiRing.*-nullʳ semiRingInt (pos n) = cong pos (*-nullʳ n)
  SemiRing.*-nullʳ semiRingInt (negsuc n) = cong (intNegate ∘ pos) (*-nullʳ n)
  SemiRing.*-distribˡ-+ semiRingInt = cheat
  SemiRing.*-distribʳ-+ semiRingInt = cheat
  {-# COMPILE AGDA2HS semiRingInt #-}

  ringInt : Ring Int
  Ring.super ringInt = semiRingInt
  Ring.negate ringInt = intNegate
  Ring.+-inverseˡ ringInt (pos zero) = refl
  Ring.+-inverseˡ ringInt (pos (suc n)) = natSubSameIsZero (suc n)
  Ring.+-inverseˡ ringInt (negsuc n) = natSubSameIsZero (suc n)
  Ring.+-inverseʳ ringInt (pos zero) = refl
  Ring.+-inverseʳ ringInt (pos (suc n)) = natSubSameIsZero (suc n)
  Ring.+-inverseʳ ringInt (negsuc n) = natSubSameIsZero (suc n)
  {-# FOREIGN AGDA2HS
  instance Ring Integer where
    negate = Prelude.negate #-}

  -- Order-related instances
  leInt : Le Int
  (leInt Le.≤ pos n) (pos n₁) = n ≤ n₁
  (leInt Le.≤ pos n) (negsuc n₁) = ⊥
  (leInt Le.≤ negsuc n) (pos n₁) = ⊤
  (leInt Le.≤ negsuc n) (negsuc n₁) = n₁ ≤ n
  {-# COMPILE AGDA2HS leInt #-}

  decLeInt : DecLe Int
  DecLe.le decLeInt = leInt
  (decLeInt DecLe.≤# pos n) (pos n₁) = n ≤# n₁
  (decLeInt DecLe.≤# pos n) (negsuc n₁) = false
  (decLeInt DecLe.≤# negsuc n) (pos n₁) = true
  (decLeInt DecLe.≤# negsuc n) (negsuc n₁) = n₁ ≤# n
  DecLe.≤#-correct decLeInt (pos n) (pos n₁) = id , id
  DecLe.≤#-correct decLeInt (pos n) (negsuc n₁) = (λ ()) , λ ()
  DecLe.≤#-correct decLeInt (negsuc n) (pos n₁) = (λ _ -> tt) , λ _ -> itsTrue
  DecLe.≤#-correct decLeInt (negsuc n) (negsuc n₁) = id , id
  {-# FOREIGN AGDA2HS
  instance DecLe Integer where
    a ≤# b = a Prelude.<= b
  #-}

  partialOrderInt : PartialOrder Int
  PartialOrder.le partialOrderInt = leInt
  PartialOrder.setoid partialOrderInt = setoidInt
  PartialOrder.≤-proper partialOrderInt _ _ _ _ refl refl P = P
  {-# COMPILE AGDA2HS partialOrderInt #-}

  ltInt : Lt Int
  (ltInt Lt.< pos n) (pos n₁) = n < n₁
  (ltInt Lt.< pos n) (negsuc n₁) = ⊥
  (ltInt Lt.< negsuc n) (pos n₁) = ⊤
  (ltInt Lt.< negsuc n) (negsuc n₁) = n₁ < n
  {-# COMPILE AGDA2HS ltInt #-}

  decLtInt : DecLt Int
  DecLt.lt decLtInt = ltInt
  (decLtInt DecLt.<# pos n) (pos n₁) = n <# n₁
  (decLtInt DecLt.<# pos n) (negsuc n₁) = false
  (decLtInt DecLt.<# negsuc n) (pos n₁) = true
  (decLtInt DecLt.<# negsuc n) (negsuc n₁) = n₁ <# n
  DecLt.<#-correct decLtInt (pos n) (pos n₁) = id , id
  DecLt.<#-correct decLtInt (pos n) (negsuc n₁) = (λ ()) , λ ()
  DecLt.<#-correct decLtInt (negsuc n) (pos n₁) = (λ _ -> tt) , λ _ -> itsTrue
  DecLt.<#-correct decLtInt (negsuc n) (negsuc n₁) = id , id
  {-# FOREIGN AGDA2HS
  instance DecLt Integer where
    a <# b = a Prelude.< b
  #-}

  pseudoOrderInt : PseudoOrder Int
  PseudoOrder.strongSetoid pseudoOrderInt = strongSetoidInt
  PseudoOrder.lt pseudoOrderInt = ltInt
  PseudoOrder.<-asym pseudoOrderInt {x} {y} x<y y<x = cheat
  PseudoOrder.<-cotrans pseudoOrderInt = cheat
  PseudoOrder.<-total pseudoOrderInt = cheat
  {-# COMPILE AGDA2HS pseudoOrderInt #-}

  absInt : Abs Int
  Abs.ring absInt = ringInt
  Abs.le absInt = leInt
  Abs.abs absInt x = pos (natAbs x)
  Abs.absCorrect absInt (pos zero) = (λ _ -> refl) , λ _ -> refl
  Abs.absCorrect absInt (pos (suc n)) = (λ _ -> refl) , λ ()
  Abs.absCorrect absInt (negsuc n) = magic , λ _ -> refl
  {-# FOREIGN AGDA2HS
  instance Abs Integer where
    abs = Prelude.abs
  #-}

  natPowInt : Pow Int Nat
  (natPowInt Pow.^ x) zero = pos (suc zero)
  (natPowInt Pow.^ x) (suc n) = x * x ^ n
  Pow.powProper natPowInt refl refl = refl
  Pow.powNull natPowInt _ = refl
  Pow.powSuc natPowInt _ _ = refl
  -- Here, we change it to a quicker implementation, too.
  {-# FOREIGN AGDA2HS
  instance Pow Integer Natural where
    n ^ k = go n k 1
      where
        go :: Integer -> Natural -> Integer -> Integer
        go base 0 res = res
        go base exp res = go (base * base) (exp `Prelude.div` 2) (if (Prelude.even exp) then res else res * base)
  #-}

{-
-- We'll need this later.
natFromNonNegInt : (x : Int) -> @0 (IsNonNegativeInteger x) -> Nat
natFromNonNegInt (pos n) _ = n
{-# COMPILE AGDA2HS natFromNonNegInt #-}
-}

-- Similarly to Naturals, we define an abstract class here.
record Integers (a : Set) : Set₁ where
  field
    overlap {{super}} : Ring a
    -- We make this a bit less general, by requiring b to be a Ring too.
    integersToRing : ∀ {b : Set} -> {{Ring b}} -> a -> b
    @0 isMorphism : ∀ {b : Set} -> {{ringb : Ring b}} ->
                                       SemiRingMorphism {a} {b} integersToRing
    @0 isUnique : ∀ {b : Set} -> {{ringb : Ring b}} ->
                     ∀ {f : a -> b} -> SemiRingMorphism {a} {b} f ->
                     (∀ (x : a) -> integersToRing x ≃ f x)          -- every function which can do the same is equivalent
open Integers {{...}} public
{-# FOREIGN AGDA2HS
class Ring a => Integers a where
  integersToRing :: Ring b => a -> b
#-}
