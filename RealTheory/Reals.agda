-- Some common operations on real number types
-- (AppRationals types in the C monad).
{-# OPTIONS --erasure #-}

module RealTheory.Reals where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, Either(..), Bool(..), id, (.))

import Operations.ShiftL
import Implementations.Int
import Implementations.Rational
import RealTheory.AppRationals
#-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim using (_∘_; id; itsTrue; if_then_else_)
open import Haskell.Prim.Either

open import Tools.Cheat

open import Tools.ErasureProduct
open import Algebra.Setoid
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
open import RealTheory.AppRationals
open import Algebra.MetricSpace
open import RealTheory.Continuity
open import Algebra.Ring
open import Algebra.Field
open import Algebra.Order
open import Operations.Decidable
open import Operations.Abs
open import Operations.Cast
open import Operations.ShiftL
open import RealTheory.Completion
open import RealTheory.Interval

-- agda2hs gets confused over this operator sometimes;
-- so we need a prefix version (simply using _:^:_ does not work there).
prefixCon : ∀ {i} {j} {a : Set i} {b : @0 a → Set j} -> (x : a) -> b x -> Σ' a b
prefixCon = _:^:_
{-# COMPILE AGDA2HS prefixCon #-}

-- First, the compress function.
-- This creates a real number equal to the original one,
-- but with simpler a's returned by the embedded function.
compress : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> C a
compress = proj₁' (bindC (prefixCon (λ x -> MkC (λ ε -> appApprox x (ratLog2Floor (proj₁ ε) {proj₂ ε})) cheat) (WrapMod id cheat)))
    --     ^ actually, any modulus would be OK here (even λ _ -> null, but that's not allowed)
{-# COMPILE AGDA2HS compress #-}

@0 compressEq : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     (x : C a) -> compress x ≃ x
compressEq = cheat

@0 NonNegR : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> Set
NonNegR {a} x = ∀ (ε : PosRational) -> negate (proj₁ ε) ≤ cast {a} {Rational} (fun x ε)

-- We need this to avoid circular dependencies.
negateR : ∀ {a : Set} {{ring : Ring a}} {{pra : PrelengthSpace a}}
                     -> C a -> C a
negateR x = MkC (negate ∘ fun x) cheat
{-# COMPILE AGDA2HS negateR #-}

-- This too.
plusR : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> C a -> C a
plusR x y = map2 (prefixCon
                    (λ x -> prefixCon
                            (λ y -> x + y)
                            (WrapMod id
                                 λ ε y₁ y₂ bεy₁y₂ ->
                                   ballReflexive ε (x + y₁) (x + y₂)
                                     cheat))
                    (WrapMod id cheat))
                    (compress x) (compress y)
{-# COMPILE AGDA2HS plusR #-}

instance
  leReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> Le (C a)
  Le._≤_ leReals x y = NonNegR (plusR y (negateR x))
  {-# COMPILE AGDA2HS leReals #-}

-- This will be the decidable criterium for a natural
-- to be a good witness for PosR.
posRCrit : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> Nat -> Bool
-- 1 << (-n)  <  x(1 << (-n-1))
posRCrit x n = ε <# cast (fun x (halvePos εpos))
  where
  -- Since we use strict inequality in PosRT,
  -- we don't need to shift the right side more.
  ε : Rational
  ε = shift (MkFrac (pos 1) (pos 1) tt) (negate (toInt (pos n)))
  εpos : PosRational
  εpos = ε :&: cheat
{-# COMPILE AGDA2HS posRCrit #-}

@0 PosR : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> Set
-- See Krebbers and Spitters' Prop-based _<_.
-- This is erased; so we cannot extract n from it.
PosR x = Σ0 Nat
      -- For technical reasons,
      -- we'll use _<#_ and _≡ true.
      -- This way, we can use witness extraction.
      (λ n -> posRCrit x n ≡ true) 

-- We'll use these later;
-- that's why we define them so early.
maxR : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> C a -> C a
maxR {a} x y = map2 (second :^: WrapMod id cheat) (compress x) (compress y)
  where
  -- We need to add constraints again for Haskell
  -- (otherwise, it believes it's a different a without constraints).
  second : ∀ {a : Set} {{ara : AppRationals a}} {{pra : MetricSpace a}}
      -> a -> UcFun a a
  second x = (λ y -> max x y) :^: WrapMod id cheat
{-# COMPILE AGDA2HS maxR #-}

minR : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> C a -> C a -> C a
minR {a} x y = map2 (second :^: WrapMod id cheat) (compress x) (compress y)
  where
  -- Same here.
  second : ∀ {a : Set} {{ara : AppRationals a}} {{pra : MetricSpace a}}
      -> a -> UcFun a a
  second x = (λ y -> min x y) :^: WrapMod id cheat
{-# COMPILE AGDA2HS minR #-}

private
  -- We'll use this for multiplication;
  -- but have to define it separately
  -- because of dirty pattern matchings.
  recipabs : Rational -> Rational
  -- ∣x∣⁻¹ if a is not null; otherwise any modulus (let's say one)
  recipabs (MkFrac (pos zero) den₁ denNotNull₁) = one
  recipabs (MkFrac (pos (suc n)) den₁ denNotNull₁)
           = MkFrac (abs den₁) (pos (suc n)) tt
  recipabs (MkFrac (negsuc n) den₁ denNotNull₁)
           = MkFrac (abs den₁) (pos (suc n)) tt
  {-# FOREIGN AGDA2HS
  recipabs :: Rational -> Rational
  recipabs (MkFrac 0 _) = MkFrac 1 1
  recipabs (MkFrac n d) = MkFrac (abs n) (abs d)
  #-}

instance
  -- We'll use this in NonZero.
  ltReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> Lt (C a)
  Lt._<_ ltReals x y = PosR (plusR y (negateR x)) 
  {-# COMPILE AGDA2HS ltReals #-}

  strongSetoidReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                       -> StrongSetoid (C a)
  StrongSetoid.super strongSetoidReals = setoidC
  StrongSetoid._><_ strongSetoidReals x y = Either (x < y) (y < x)
  StrongSetoid.><-irrefl strongSetoidReals = cheat
  StrongSetoid.><-sym strongSetoidReals = cheat
  StrongSetoid.><-cotrans strongSetoidReals = cheat
  StrongSetoid.><-tight-apart strongSetoidReals = cheat
  {-# COMPILE AGDA2HS strongSetoidReals #-}

  semiRingReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> SemiRing (C a)
  SemiRing.super semiRingReals = setoidC
  -- TODO: we should rewrite this with map2.
  SemiRing._+_ (semiRingReals {a} {{ara = ara}} {{pra = pra}})
                                 = plusR
  -- Now, we have to find a rational c such that y ∈ [-c,c].
  SemiRing._*_ (semiRingReals {a}) x y = let cx = compress x; cy = compress y in
                            map2 {{prb = prelengthInterval {a} {I}}}
                                  (prefixCon
                                     (λ a -> secondFun a)
                                     (WrapMod (λ ε -> proj₁ ε * recip (cast c) cheat :&: cheat) cheat)) cx
     -- This simply converts cy to the Σ0 version.
     (MkC (λ ε -> fun cy ε :&: cheat) cheat)
    where
    c : a
    c = abs (fun (compress y) (one :&: itsTrue)) + one
    @0 I : Interval a
    I = [ negate c , c ]
    secondFun : (x : a) -> UcFun (Σ0 a (IsIn I)) a
    secondFun x = prefixCon (λ sy -> x * proj₁ sy) (WrapMod (λ ε -> proj₁ ε * recipabs (cast x)
                                     :&: cheat) cheat)
  SemiRing.+-proper semiRingReals = cheat
  SemiRing.+-assoc semiRingReals = cheat
  SemiRing.*-proper semiRingReals = cheat
  SemiRing.*-assoc semiRingReals = cheat
  SemiRing.null semiRingReals = returnC null
  SemiRing.one semiRingReals = returnC one
  SemiRing.NonZero semiRingReals x = null >< x -- positive or negative
  SemiRing.NonZeroCorrect semiRingReals = cheat
  SemiRing.NonZeroOne semiRingReals = cheat
  SemiRing.+-identityˡ semiRingReals = cheat
  SemiRing.+-identityʳ semiRingReals = cheat
  SemiRing.*-identityˡ semiRingReals = cheat
  SemiRing.*-identityʳ semiRingReals = cheat
  SemiRing.+-comm semiRingReals = cheat
  SemiRing.*-comm semiRingReals = cheat
  SemiRing.*-nullˡ semiRingReals = cheat
  SemiRing.*-nullʳ semiRingReals = cheat
  SemiRing.*-distribˡ-+ semiRingReals = cheat
  SemiRing.*-distribʳ-+ semiRingReals = cheat
  {-# COMPILE AGDA2HS semiRingReals #-}

  ringReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> Ring (C a)
  Ring.super ringReals = semiRingReals
  Ring.negate ringReals = negateR
  Ring.+-inverseˡ ringReals = cheat
  Ring.+-inverseʳ ringReals = cheat
  {-# COMPILE AGDA2HS ringReals #-}

  absReals : ∀ {a : Set} {{ara : AppRationals a}} {{metric : PrelengthSpace a}}
                     -> Abs (C a)
  Abs.ring absReals = ringReals
  Abs.le absReals = leReals
  Abs.abs absReals x = MkC (λ ε -> abs (fun x ε)) λ ε₁ ε₂ -> cheat
  Abs.absCorrect absReals = cheat
  {-# COMPILE AGDA2HS absReals #-}

  castCRat : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                 -> Cast (C a) (C Rational)
  Cast.cast castCRat x = MkC (λ ε -> cast (fun x ε)) cheat
  {-# COMPILE AGDA2HS castCRat #-}

-- A positivity predicate where the witness is not erased.
PosRT : ∀ {@0 a : Set} {{@0 ara : AppRationals a}} {{@0 pra : PrelengthSpace a}}
                      -> @0 C a -> Set
PosRT x = Σ0 PosRational λ ε -> proj₁ ε < cast (fun x ε)
{-# COMPILE AGDA2HS PosRT #-}

NonZeroRT : ∀ {@0 a : Set} {{@0 ara : AppRationals a}} {{@0 pra : PrelengthSpace a}}
                      -> @0 C a -> Set
NonZeroRT x = Either (PosRT x) (PosRT (negate x))
{-# COMPILE AGDA2HS NonZeroRT #-}

-- A _<_ based on that.
LtT : ∀ {@0 a : Set} {{@0 ara : AppRationals a}} {{@0 pra : PrelengthSpace a}}
                      -> @0 C a -> @0 C a -> Set
LtT x y = PosRT (y + negate x)
{-# COMPILE AGDA2HS LtT #-}

-- Creating a non-erased natural existence proof from an erased one
-- (essentially, calculating a witness)
-- if the property is decidable.
-- This is needed for the inverse.
-- I don't yet know how we could prove the termination of this.
{-# TERMINATING #-}
witness : ∀ (p : Nat -> Bool) (@0 erasedProof : Σ0 Nat (λ n -> p n ≡ true))
                -> Σ0 Nat (λ n -> p n ≡ true)
witness p (n :&: hyp) = go 1 n
  where
  -- Could we use this to prove termination somehow?
  @0 pred : Nat -> Nat
  pred zero = zero
  pred (suc n) = n
  
  go : Nat -> @0 Nat -> Σ0 Nat (λ n -> p n ≡ true)
  go n n0 with p n in eq
  ... | true = n :&: eq
  ... | false = go (suc n) (pred n0)
-- Tried it with if-then-else, but then it got stuck at the next one.
{-# FOREIGN AGDA2HS
-- Here we go faster, by shifting leftwards and thus increasing it exponentially
-- instead of just incrementing by one.
witness :: (Natural -> Bool) -> Σ0 Natural
witness p = (:&:) (Prelude.until p (\ n -> shiftl n (1 :: Natural)) 1)
#-}

witnessForPos : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> (x : C a) -> @0 (PosR x) -> PosRT x
witnessForPos x hyp = ε :&: cheat
  where
  natPack : Σ0 Nat (λ n → posRCrit (MkC (fun x) (reg x)) n ≡ true)
  natPack = witness (posRCrit x) hyp
  n : Nat
  n = proj₁ natPack
  ε : PosRational
  ε = shift (MkFrac (pos 1) (pos 1) tt) (toInt (negsuc n))
           :&: cheat
{-# COMPILE AGDA2HS witnessForPos #-}

witnessForNonZero : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> (x : C a) -> @0 (NonZero x) -> NonZeroRT x
witnessForNonZero x hyp = sol
  where
  εPack : PosRT (abs x)
  εPack = witnessForPos (abs x) cheat
  ε : PosRational
  ε = proj₁ εPack
  -- We check if it's good for x; if not, it will be good for negate x.
  sol : NonZeroRT x
  sol = if (proj₁ ε <# cast (fun x ε)) then Left (ε :&: cheat) else Right (ε :&: cheat)
  {-with proj₁ ε <# cast (fun x ε) in eq
  ... | true = Left (ε :&: cheat)
  ... | false = Right (ε :&: cheat)-}
-- {-# COMPILE AGDA2HS witnessForNonZero #-}
-- Here, strange things happen; I think that might be a bug in agda2hs.
{-# FOREIGN AGDA2HS
witnessForNonZero ::
                    (AppRationals a, PrelengthSpace a) => C a -> NonZeroRT
witnessForNonZero x = sol
  where
    εPack :: PosRT
    εPack = witnessForPos (abs x)
    ε :: PosRational
    ε = proj₁ εPack
    sol :: NonZeroRT
    sol
      = if proj₁ ε <# cast (fun x ε) then Left (ε :&:) else Right (ε :&:)
#-}

instance
  fieldReals : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                     -> Field (C a)
  Field.ring fieldReals = ringReals
  Field.strongSetoid fieldReals = strongSetoidReals
  Field.+-strong-proper fieldReals = cheat
  Field.*-strong-proper fieldReals = cheat
  Field.recip (fieldReals {a}) x hyp =
                             -- v I'm not sure whether this is true in general
          proj₁' (bindC {{psa = prelengthΣ0 {a} {λ x -> IsIn I (cast x)}}} toLift)
                    (MkC (λ ε -> fun (compress x) ε :&: cheat) (reg (compress x)))
    where
    tPack : NonZeroRT x
    tPack = witnessForNonZero x hyp
    isPositive : {@0 x : C a} -> NonZeroRT x -> Bool
    isPositive (Left _) = true
    isPositive (Right _) = false
    extractWitness : {@0 x : C a} -> NonZeroRT x -> PosRational
    extractWitness (Left (tpos :&: _)) = tpos
    extractWitness (Right (tpos :&: _)) = tpos
    t : PosRational
    t = extractWitness {x} tPack
    @0 I : Interval Rational
    I = if (isPositive {x} tPack) then [ proj₁ t ,+∞[ else ]-∞, negate (proj₁ t) ]
    @0 INonZero : ∀ {q : Rational} -> IsIn I q -> NonZero q
    INonZero = cheat
    toLift : UcFun (Σ0 a (λ x -> IsIn I (cast x))) (C a)
    toLift = prefixCon
               (λ sx -> let x = proj₁ sx in
                   MkC (λ ε -> appDiv one x cheat (ratLog2Floor (proj₁ ε) {proj₂ ε})) cheat)
               (WrapMod (λ _ -> t) cheat)
  Field.recip-proper fieldReals = cheat
  Field.*-inverseˡ fieldReals = cheat
  Field.*-inverseʳ fieldReals = cheat
  {-# COMPILE AGDA2HS fieldReals #-}
