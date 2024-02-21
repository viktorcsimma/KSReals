-- Some common operations on real number types
-- (AppRational types in the C monad).
{-# OPTIONS --erasure #-}

module RealTheory.Real where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, Either(..), Bool(..), id, (.))

import Operator.ShiftL
import Operator.Shift
import Implementation.Int
import Implementation.Rational
import RealTheory.AppRational
#-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim using (_∘_; id; itsTrue; if_then_else_)
open import Haskell.Prim.Either

open import Tool.Cheat

open import Tool.ErasureProduct
open import Algebra.Setoid
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import RealTheory.AppRational
open import RealTheory.MetricSpace
open import RealTheory.Continuity
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Field
open import Algebra.Order
open import Operator.Decidable
open import Operator.Abs
open import Operator.Cast
open import Operator.ShiftL
open import Operator.Shift
open import Operator.ExactShift
open import RealTheory.Completion
open import RealTheory.Interval

-- First, the compress function.
-- This creates a real number equal to the original one,
-- but with simpler a's returned by the embedded function.
compress : ∀ {a : Set} {{ara : AppRational a}}
                     -> C a -> C a
compress = proj₁' (bindC (prefixCon (λ x -> MkC (λ ε -> appApprox x (ratLog2Floor (proj₁ ε) {proj₂ ε})) λ ε₁ ε₂ -> cheat) (WrapMod id cheat)))
    --     ^ actually, any modulus would be OK here (even λ _ -> null, but that's not allowed)
{-# COMPILE AGDA2HS compress #-}

@0 compressEq : ∀ {a : Set} {{ara : AppRational a}}
                     (x : C a) -> compress x ≃ x
compressEq = cheat

@0 NonNegR : ∀ {a : Set} {{ara : AppRational a}}
                     -> C a -> Set
NonNegR {a} x = ∀ (ε : PosRational) -> negate (proj₁ ε) ≤ cast {a} {Rational} (fun x ε)

-- We need this to avoid circular dependencies.
negateR : ∀ {a : Set} {{ring : Ring a}} {{metricSpace : MetricSpace a}}
                     -> C a -> C a
negateR x = MkC (negate ∘ fun x) cheat
{-# COMPILE AGDA2HS negateR #-}

-- This too.
plusR : ∀ {a : Set} {{ara : AppRational a}}
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
  leReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> Le (C a)
  Le._≤_ leReals x y = NonNegR (plusR y (negateR x))
  {-# COMPILE AGDA2HS leReals #-}

-- This will be the decidable criterium for a natural
-- to be a good witness for PosR.
posRCrit : ∀ {a : Set} {{ara : AppRational a}}
                     -> C a -> Nat -> Bool
-- 1 << (-n)  <  x(1 << (-n-1))
posRCrit x n = ε <# cast (fun x (halvePos εpos))
  where
  -- Since we use strict inequality in PosRT,
  -- we don't need to shift the right side more.
  ε : Rational
  ε = shift (MkFrac (pos 1) (pos 1) tt) (negate (pos n))
  εpos : PosRational
  εpos = ε :&: cheat
{-# COMPILE AGDA2HS posRCrit #-}

@0 PosR : ∀ {a : Set} {{ara : AppRational a}}
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
maxR : ∀ {a : Set} {{ara : AppRational a}}
                     -> C a -> C a -> C a
maxR {a} x y = map2 (second :^: WrapMod id cheat) (compress x) (compress y)
  where
  -- We need to add constraints again for Haskell
  -- (otherwise, it believes it's a different a without constraints).
  second : ∀ {a : Set} {{ara : AppRational a}}
      -> a -> UcFun a a
  second x = (λ y -> max x y) :^: WrapMod id cheat
{-# COMPILE AGDA2HS maxR #-}

minR : ∀ {a : Set} {{ara : AppRational a}}
                     -> C a -> C a -> C a
minR {a} x y = map2 (second :^: WrapMod id cheat) (compress x) (compress y)
  where
  -- Same here.
  second : ∀ {a : Set} {{ara : AppRational a}}
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
  ltReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> Lt (C a)
  Lt._<_ ltReals x y = PosR (plusR y (negateR x)) 
  {-# COMPILE AGDA2HS ltReals #-}

  strongSetoidReals : ∀ {a : Set} {{ara : AppRational a}}
                       -> StrongSetoid (C a)
  StrongSetoid.super strongSetoidReals = setoidC
  StrongSetoid._><_ strongSetoidReals x y = Either (x < y) (y < x)
  StrongSetoid.><-irrefl strongSetoidReals = cheat
  StrongSetoid.><-sym strongSetoidReals = cheat
  StrongSetoid.><-cotrans strongSetoidReals = cheat
  StrongSetoid.><-tight-apart strongSetoidReals = cheat
  {-# COMPILE AGDA2HS strongSetoidReals #-}

  semiRingReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> SemiRing (C a)
  SemiRing.super semiRingReals = setoidC
  -- TODO: we should rewrite this with map2.
  SemiRing._+_ (semiRingReals {a} {{ara = ara}})
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
    c = abs (fun (compress y) (one :&: cheat)) + one
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

  ringReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> Ring (C a)
  Ring.super ringReals = semiRingReals
  Ring.negate ringReals = negateR
  Ring.+-inverseˡ ringReals = cheat
  Ring.+-inverseʳ ringReals = cheat
  {-# COMPILE AGDA2HS ringReals #-}

  absReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> Abs (C a)
  Abs.ring absReals = ringReals
  Abs.le absReals = leReals
  Abs.abs absReals x = MkC (λ ε -> abs (fun x ε)) λ ε₁ ε₂ -> cheat
  Abs.absCorrect absReals = cheat
  {-# COMPILE AGDA2HS absReals #-}

  castCRat : ∀ {a : Set} {{ara : AppRational a}}
                 -> Cast (C a) (C Rational)
  Cast.cast castCRat x = MkC (λ ε -> cast (fun x ε)) cheat
  {-# COMPILE AGDA2HS castCRat #-}

-- A positivity predicate where the witness is not erased.
PosRT : ∀ {@0 a : Set} {{@0 ara : AppRational a}}
                      -> @0 C a -> Set
PosRT x = Σ0 PosRational λ ε -> proj₁ ε < cast (fun x ε)
{-# COMPILE AGDA2HS PosRT #-}

NonZeroRT : ∀ {@0 a : Set} {{@0 ara : AppRational a}}
                      -> @0 C a -> Set
NonZeroRT x = Either (PosRT x) (PosRT (negate x))
{-# COMPILE AGDA2HS NonZeroRT #-}

-- A _<_ based on that.
LtT : ∀ {@0 a : Set} {{@0 ara : AppRational a}}
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
-- Since posRCrit already uses shifting,
-- we go here incrementally, too.
-- This way, it remains correct
-- even if there is only a finite amount of good witnesses.
witness :: (Natural -> Bool) -> Σ0 Natural
witness p = (:&:) (Prelude.until p (1 +) 1)
#-}

witnessForPos : ∀ {a : Set} {{ara : AppRational a}}
                     -> (x : C a) -> @0 (PosR x) -> PosRT x
witnessForPos x hyp = ε :&: cheat
  where
  natPack : Σ0 Nat (λ n → posRCrit (MkC (fun x) (reg x)) n ≡ true)
  natPack = witness (posRCrit x) hyp
  n : Nat
  n = proj₁ natPack
  ε : PosRational
  ε = shift (MkFrac (pos 1) (pos 1) tt) (negsuc n)
           :&: cheat
{-# COMPILE AGDA2HS witnessForPos #-}

witnessForNonZero : ∀ {a : Set} {{ara : AppRational a}}
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
                    (AppRational a) => C a -> NonZeroRT
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
  fieldReals : ∀ {a : Set} {{ara : AppRational a}}
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
               (WrapMod (λ ε -> proj₁ ε * proj₁ t * proj₁ t :&: cheat) cheat) -- are you sure?
                                                                     -- O'Connor writes this,
                                                                     -- but maybe AppRational kick in
  Field.recip-proper fieldReals = cheat
  Field.*-inverseˡ fieldReals = cheat
  Field.*-inverseʳ fieldReals = cheat
  {-# COMPILE AGDA2HS fieldReals #-}

-- For shifting.
-- We can use O'Connor's Theorem 29 here about multiplying with a constant.
private
  realShift : ∀ {a : Set} {{ara : AppRational a}} -> C a -> Int -> C a
  realShift x n = mapC
                    (prefixCon
                       (λ a -> shift a n)
                       (WrapMod (λ ε -> shift (proj₁ ε) (negate n) :&: cheat)
                               cheat))
                    x
  {-# COMPILE AGDA2HS realShift #-}

instance
  shiftLReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> ShiftL (C a)
  ShiftL.semiringa shiftLReals = semiRingReals
  -- Maybe we should collect these uniformly continuous functions somewhere.
  ShiftL.shiftl shiftLReals x n = realShift x (pos n)
  ShiftL.shiftlProper shiftLReals = cheat
  ShiftL.shiftlNull shiftLReals = cheat
  ShiftL.shiftlSuc shiftLReals = cheat
  {-# COMPILE AGDA2HS shiftLReals #-}

  -- Similarly.
  shiftReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> Shift (C a)
  Shift.super shiftReals = shiftLReals
  Shift.shift shiftReals = realShift
  Shift.shiftProper shiftReals = cheat
  Shift.shiftEquivalent shiftReals = cheat
  Shift.shiftLeftThenRight shiftReals = cheat
  {-# COMPILE AGDA2HS shiftReals #-}

  exactShiftReals : ∀ {a : Set} {{ara : AppRational a}}
                     -> ExactShift (C a)
  ExactShift.super exactShiftReals = shiftReals
  ExactShift.shiftRightThenLeft exactShiftReals = cheat
  {-# COMPILE AGDA2HS exactShiftReals #-}

-- And actually, if we are here,
-- let's write a multiplication function
-- with a constant AQ.
multByAQ : ∀ {a : Set} {{ara : AppRational a}}
                 -> a -> C a -> C a
multByAQ a = mapC ((λ b -> a * b) :^: WrapMod
                                        (λ ε -> multPos ε
                                                        ((if a ≃# null then (one :&: cheat) else (recip (cast (abs a)) cheat) :&: cheat)))
                                        cheat)
{-# COMPILE AGDA2HS multByAQ #-}

@0 multByAQCorrect : ∀ {a : Set} {{ara : AppRational a}}
                         -> (q : a) (x : C a)
                         -> multByAQ q x ≃ returnC q * x
multByAQCorrect = cheat

-- The canonical bound is an AQ which is guaranteed to be greater than or equal to x.
-- Sometimes, it's more beneficial for it to be even negative;
-- e.g. when we need an interval like ]-∞, canonicalBound x ].
-- But you can use canonicalBound (abs x) if you need that.
canonicalBound : ∀ {a : Set} {{ara : AppRational a}}
                     (x : C a) -> a
canonicalBound x = fun (compress x) (one :&: cheat) + one
{-# COMPILE AGDA2HS canonicalBound #-}

@0 canonicalBoundCorrect : ∀ {a : Set} {{ara : AppRational a}}
                           -> ∀ (x : C a)
                           -> x ≤ returnC (canonicalBound x)
canonicalBoundCorrect = cheat
