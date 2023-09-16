-- Instances for the builtin Int type.
module Int where

{-# FOREIGN AGDA2HS
{-# LANGUAGE MultiParamTypeClasses #-}
import qualified Prelude
import Data.Bits (shift) #-}

open import Cheat

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
import Agda.Builtin.Nat
open Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.Equality
open import Haskell.Prim using (⊥; _∘_; magic; ltNat; addNat; id; itsTrue)
open import Haskell.Prim.Tuple
open import Haskell.Prim.Integer using (IsNonNegativeInteger)

open import PropositionalEquality
open import Setoid
open import Decidable
import Ring
open Ring hiding (_+_; _*_)
open import Nat
open import Order
open import Operations

-- Here, the operators are not pre-defined;
-- so we have to copy them from the standard library.

private
  infixl 7 _*_
  infixl 6 _+_

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

  _+_ : Int -> Int -> Int
  pos x + pos y = pos (x Agda.Builtin.Nat.+ y)
  pos x + negsuc y = natSub x (suc y)
  negsuc x + pos y = natSub y (suc x)
  negsuc x + negsuc y = negsuc (suc (x Agda.Builtin.Nat.+ y))
  -- We won't compile this. Instead, we'll use Haskell's builtin operators.

  -- Now multiplication. We won't compile this either.
  _*_ : Int -> Int -> Int
  pos n * pos n₁ = pos (n Agda.Builtin.Nat.* n₁)
  pos n * negsuc n₁ = intNegate (pos (n Agda.Builtin.Nat.* suc n₁))
  negsuc n * pos n₁ = intNegate (pos (suc n Agda.Builtin.Nat.* n₁))
  negsuc n * negsuc n₁ = pos (suc n Agda.Builtin.Nat.* suc n₁)

  -- 0.5 will be rounded to 0;
  -- -0.5 to -1.
  -- So like in Python.
  halveInt : Int -> Int
  halveInt (pos n) = pos (halveNat n)
  halveInt (negsuc n) = negsuc (halveNat n)

  @0 _≢+0 : Int -> Set
  pos zero ≢+0 = ⊥
  _        ≢+0 = ⊤

infixl 7 _intDiv_
-- Now this has to be public.
_intDiv_ : (x y : Int) -> @0 {y ≢+0} -> Int
_intDiv_ (pos m) (pos (suc n)) = pos (m natDiv (suc n))
_intDiv_ (pos m) (negsuc n) = intNegate (pos (m natDiv suc n))
_intDiv_ (negsuc m) (pos (suc n)) = intNegate (pos (suc m natDiv suc n))
_intDiv_ (negsuc m) (negsuc n) = pos (suc m natDiv suc n)
-- And we will use `quot` in Haskell (this rounds towards zero).
-- (`div` would be uglier now.)

natAbs : Int -> Nat
natAbs (pos n) = n
natAbs (negsuc n) = suc n
{-# FOREIGN AGDA2HS
natAbs :: Integer -> Natural
natAbs = fromInteger . Prelude.abs
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
    (≃#) = (==)
  #-}

  strongSetoidInt : StrongSetoid Int
  StrongSetoid.super strongSetoidInt = setoidInt
  StrongSetoid._><_ strongSetoidInt x y = x ≡ y -> ⊥
  StrongSetoid.><-irrefl strongSetoidInt eq neq = neq eq
  StrongSetoid.><-sym strongSetoidInt neq refl = neq refl
  StrongSetoid.><-cotrans strongSetoidInt neqxy z = cheat  -- I think _≡_ is decidable; isn't it?
  StrongSetoid.><-tight-apart strongSetoidInt = cheat , λ eq neq -> neq eq
  {-# COMPILE AGDA2HS strongSetoidInt #-}

  trivialApartInt : TrivialApart Int
  TrivialApart.super trivialApartInt = strongSetoidInt
  TrivialApart.trivialApart trivialApartInt x y = id , id
  {-# COMPILE AGDA2HS trivialApartInt #-}

  semiRingInt : SemiRing Int
  SemiRing.super semiRingInt = setoidInt
  SemiRing._+_ semiRingInt = _+_
  SemiRing._*_ semiRingInt = _*_
  SemiRing.+-proper semiRingInt refl refl = refl
  SemiRing.+-assoc semiRingInt x y z = cheat
  SemiRing.*-proper semiRingInt refl refl = refl
  SemiRing.*-assoc semiRingInt x y z = cheat
  SemiRing.null semiRingInt = pos zero
  SemiRing.one semiRingInt = pos (suc zero)
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
  {-# COMPILE AGDA2HS ringInt #-}

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
    (≤#) = (<=)
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
    (<#) = Prelude.(<)
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
        go base exp res = go (base * base) (exp `div` 2) (if (even exp) then res else res * base)
  #-}

  natShiftLInt : ShiftL Int Nat
  ShiftL.semiringa natShiftLInt = semiRingInt
  ShiftL.semiringb natShiftLInt = semiRingNat
  ShiftL.shiftl natShiftLInt x k = x * (pos 2) ^ k
  ShiftL.shiftlProper natShiftLInt _ _ _ _ refl refl = refl
  ShiftL.shiftlNull natShiftLInt x = *-identityʳ x
  ShiftL.shiftlSuc natShiftLInt x y = cheat
  -- Actually, there is a builtin shift function in Data.Bits.
  {-# FOREIGN AGDA2HS
  instance ShiftL Integer Natural where
    shiftl x k = shift x (fromIntegral k)
  #-}

  -- We need an integer shift operation, too.
  -- Of course, if the integer is negative, we will have to round.
  -- E.g. 4.5 will be rounded to 4; -0.5 to -1.
  intShiftLInt : ShiftL Int Int
  ShiftL.semiringa intShiftLInt = semiRingInt
  ShiftL.semiringb intShiftLInt = semiRingInt
  ShiftL.shiftl intShiftLInt x (pos zero) = x
  ShiftL.shiftl intShiftLInt (pos zero) _ = pos zero   -- stop if it's already zero
  ShiftL.shiftl intShiftLInt x (pos n) = shiftl x n
  ShiftL.shiftl intShiftLInt x (negsuc zero) = halveInt x
  ShiftL.shiftl intShiftLInt x (negsuc (suc n)) = shiftl (halveInt x) (negsuc n)
  ShiftL.shiftlProper intShiftLInt _ _ _ _ refl refl = refl
  ShiftL.shiftlNull intShiftLInt x = refl
  ShiftL.shiftlSuc intShiftLInt x n = cheat
  {-# FOREIGN AGDA2HS
  -- There is a builtin shift function in Data.Bits.
  instance ShiftL Int Int where
    shiftl = shift
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
