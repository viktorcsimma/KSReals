-- An implementation of fractions of semirings
-- and the rationals.
module Rational where

{-# FOREIGN AGDA2HS {-# LANGUAGE MultiParamTypeClasses #-} #-}

open import Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim using (⊥; id)
open import Haskell.Prim.Tuple

open import ErasureProduct
open import PropositionalEquality
import Nat
open import Int
open import Setoid
open import Ring
open import Field
open import Order
open import Decidable
open import Operations
open import Cast

-- Since we don't use classes below SemiRing to maintain
-- Haskell compatibility (by avoiding to give operators as parameters);
-- the constraint here is SemiRing a.
record Frac (a : Set) {{semiRing : SemiRing a}} : Set where
  constructor MkFrac
  field
    num den : a
    @0 denNotNull : NonZero den
open Frac public
{-# COMPILE AGDA2HS Frac #-}

-- Now the instances.

instance
  -- But hey, how is this going to be compiled to Haskell?
  {-
  -- Of course, we can extract a Setoid instance from a SemiRing instance;
  -- we'll do this in defaultSetoidFrac.
  -- However, sometimes we need the Setoid instance extracted from another
  -- instance argument (e. g. strongSetoidFrac).
  -- Therefore, we define this separately.
  -- And here, the Setoid argument is made explicit.
  setoidFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {setoid : Setoid} a -> Setoid (Frac a)
  Setoid._≃_ (setoidFrac setoid) x y = _≃_ {{setoid}} (num x * den y) (num y * den x)
  Setoid.≃-refl (setoidFrac setoid) {x} = ≃-refl {{setoid}} {x = num x * den x}
  Setoid.≃-sym (setoidFrac setoid) {x} {y} = {!≃-sym {{setoid}} {x = num x * den y} {y = num y * den x}!}
  Setoid.≃-trans (setoidFrac setoid) = {!!}
  -}

  setoidFrac : ∀ {a : Set} {{semiRing : SemiRing a}} -> Setoid (Frac a)
  Setoid._≃_ (setoidFrac {a}) x y = num x * den y ≃ num y * den x
  Setoid.≃-refl (setoidFrac {a}) {x} = ≃-refl {x = num x * den x}
  Setoid.≃-sym (setoidFrac {a}) {x} {y} = ≃-sym {x = num x * den y} {y = num y * den x}
  -- num x * den z = 
  Setoid.≃-trans (setoidFrac {a}) {x} {y} {z} x≃y y≃z = cheat
  {-# COMPILE AGDA2HS setoidFrac #-}

  -- Here come the problems.
  -- It wants to use the _≃_ from the SemiRing instance,
  -- and I don't know how to convince it that it's equal
  -- to the one in the StrongSetoid instance.
  strongSetoidFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{strongSetoid : StrongSetoid a}}
                                     -> StrongSetoid (Frac a)
  StrongSetoid.super (strongSetoidFrac {{strongSetoid = strongSetoid}}) = setoidFrac
  StrongSetoid._><_ strongSetoidFrac x y = num x * den y >< num y * den x
  StrongSetoid.><-irrefl strongSetoidFrac = cheat
  StrongSetoid.><-sym strongSetoidFrac {x} {y} = ><-sym {x = num x * den y} {y = num y * den x}
  StrongSetoid.><-cotrans strongSetoidFrac = cheat
  StrongSetoid.><-tight-apart strongSetoidFrac = cheat
  {-# COMPILE AGDA2HS strongSetoidFrac #-}

  semiRingFrac : ∀ {a : Set} {{semiRing : SemiRing a}} -> SemiRing (Frac a)
  SemiRing.super semiRingFrac = setoidFrac
  SemiRing._+_ semiRingFrac x y = MkFrac (num x * den y + num y * den x) (den x * den y) cheat
  SemiRing._*_ semiRingFrac x y = MkFrac (num x * num y) (den x * den y) cheat
  SemiRing.+-proper semiRingFrac = cheat
  SemiRing.+-assoc semiRingFrac = cheat
  SemiRing.*-proper semiRingFrac = cheat
  SemiRing.*-assoc semiRingFrac = cheat
  SemiRing.null (semiRingFrac {a}) = MkFrac null one NonZeroOne
  SemiRing.one (semiRingFrac {a}) = MkFrac one one NonZeroOne
  SemiRing.NonZero (semiRingFrac {a}) x = NonZero (num x)
  SemiRing.NonZeroCorrect (semiRingFrac {a}) x = cheat
  SemiRing.NonZeroOne (semiRingFrac {a}) = NonZeroOne {a}
  SemiRing.+-identityˡ semiRingFrac x = cheat
  SemiRing.+-identityʳ semiRingFrac = cheat
  -- one * num x * den x ≃ num x * (one * den x)
  SemiRing.*-identityˡ semiRingFrac x = cheat
  SemiRing.*-identityʳ semiRingFrac = cheat
  SemiRing.+-comm semiRingFrac = cheat
  SemiRing.*-comm semiRingFrac = cheat
  SemiRing.*-nullˡ semiRingFrac = cheat
  SemiRing.*-nullʳ semiRingFrac = cheat
  SemiRing.*-distribˡ-+ semiRingFrac = cheat
  SemiRing.*-distribʳ-+ semiRingFrac = cheat
  {-# COMPILE AGDA2HS semiRingFrac #-}

  ringFrac : ∀ {a : Set} {{ring : Ring a}} -> Ring (Frac a)
  Ring.super ringFrac = semiRingFrac
  Ring.negate ringFrac x = MkFrac (negate (num x)) (den x) (denNotNull x)
  Ring.+-inverseˡ ringFrac x = cheat
  Ring.+-inverseʳ ringFrac = cheat
  {-# COMPILE AGDA2HS ringFrac #-}

  -- It's enough that a is a ring and a strong setoid; it need not be a field.
  fieldFrac : ∀ {a : Set} {{ring : Ring a}} {{trivApart : TrivialApart a}}
                                              -> Field (Frac a)
  Field.ring fieldFrac = ringFrac
  Field.strongSetoid fieldFrac = strongSetoidFrac
  Field.+-strong-proper fieldFrac x y z w apart = cheat  -- can we use the former instance?
  Field.*-strong-proper fieldFrac x y z w apart = cheat
  Field.recip (fieldFrac {a}) x nApNull = MkFrac (den x) (num x) cheat -- {!fst (trivialApart (num x) null) nApNull!}
  Field.recip-proper fieldFrac xApNull yApNull = cheat
  Field.*-inverseˡ fieldFrac xApNull = cheat
  Field.*-inverseʳ fieldFrac xApNull = cheat
  {-# COMPILE AGDA2HS fieldFrac #-}

  -- Order instances
  leFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{le : Le a}} -> Le (Frac a)
  Le._≤_ leFrac x y = num x * den y ≤ num y * den x
  {-# COMPILE AGDA2HS leFrac #-}

  decLeFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{decLe : DecLe a}} -> DecLe (Frac a)
  DecLe.le decLeFrac = leFrac
  DecLe._≤#_ decLeFrac x y = num x * den y ≤# num y * den x
  DecLe.≤#-correct decLeFrac x y = ≤#-correct (num x * den y) (num y * den x)
  {-# COMPILE AGDA2HS decLeFrac #-}

  partialOrderFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{partialOrder : PartialOrder a}}
                            -> PartialOrder (Frac a)
  PartialOrder.le partialOrderFrac = leFrac
  PartialOrder.setoid partialOrderFrac = setoidFrac
  PartialOrder.≤-proper partialOrderFrac = cheat
  {-# COMPILE AGDA2HS partialOrderFrac #-}

  ltFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{lt : Lt a}} -> Lt (Frac a)
  Lt._<_ ltFrac x y = num x * den y < num y * den x
  {-# COMPILE AGDA2HS ltFrac #-}

  decLtFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{decLt : DecLt a}} -> DecLt (Frac a)
  DecLt.lt decLtFrac = ltFrac
  DecLt._<#_ decLtFrac x y = num x * den y <# num y * den x
  DecLt.<#-correct decLtFrac x y = <#-correct (num x * den y) (num y * den x)
  {-# COMPILE AGDA2HS decLtFrac #-}

  strictOrderFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{strictOrder : StrictOrder a}}
                                      -> StrictOrder (Frac a)
  StrictOrder.lt strictOrderFrac = ltFrac
  StrictOrder.setoid strictOrderFrac = setoidFrac
  -- Even here, it would like to use the Setoid instance from semiRing, not from strictOrder.
  -- I don't yet understand why; <-irrefl should specifically work with the strictOrder instance.
  StrictOrder.<-irrefl strictOrderFrac {x} {y} x≃y = <-irrefl {x = num x * den y} {y = num y * den x} cheat
  StrictOrder.<-trans strictOrderFrac = cheat
  StrictOrder.<-proper strictOrderFrac = cheat
  {-# COMPILE AGDA2HS strictOrderFrac #-}

  pseudoOrderFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{pseudoOrder : PseudoOrder a}}
                                      -> PseudoOrder (Frac a)
  PseudoOrder.strongSetoid pseudoOrderFrac = strongSetoidFrac
  PseudoOrder.lt pseudoOrderFrac = ltFrac
  PseudoOrder.<-asym pseudoOrderFrac {x} {y} = <-asym {x = num x * den y} {y = num y * den x}
  PseudoOrder.<-cotrans pseudoOrderFrac x<y z = cheat
  PseudoOrder.<-total pseudoOrderFrac = cheat
  {-# COMPILE AGDA2HS pseudoOrderFrac #-}

  trivialApartFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{trivialApart : TrivialApart a}}
                                      -> TrivialApart (Frac a)
  TrivialApart.super trivialApartFrac = strongSetoidFrac
  TrivialApart.trivialApart trivialApartFrac x y = cheat
                      {-{!trivialApart (num x * den y) (num y * den x)!}-}
  {-# COMPILE AGDA2HS trivialApartFrac #-}

  -- Here we need negate from Ring.
  absFrac : ∀ {a : Set} {{ring : Ring a}} {{le : Le a}} {{absa : Abs a}}
                                      -> Abs (Frac a)
  Abs.ring absFrac = ringFrac
  Abs.le (absFrac {a} {{ring}} {{le}}) = leFrac {a} {{_}} {{le}}
  Abs.abs absFrac (MkFrac numx denx denNotNullx) = MkFrac (abs numx) (abs denx) cheat
  Abs.absCorrect absFrac x = cheat
  {-# COMPILE AGDA2HS absFrac #-}

  castFrac : ∀ {a : Set} {{semiRing : SemiRing a}} -> Cast a (Frac a)
  Cast.cast (castFrac {a}) x = MkFrac x one (NonZeroOne {a})
  {-# COMPILE AGDA2HS castFrac #-}

  {-
  How can we assure that num x is not null?
  intPowFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{natPow : Pow a Nat}} -> Pow (Frac a) Int
  (intPowFrac Pow.^ x) (pos n) = MkFrac (num x ^ n) (den x ^ n) cheat
  (intPowFrac Pow.^ x) (negsuc n) = {!MkFrac (!}
  Pow.powProper intPowFrac = {!!}
  Pow.powNull intPowFrac = {!!}
  Pow.powSuc intPowFrac = {!!}
  {-# COMPILE AGDA2HS intPowFrac #-}
  -}

  shiftLFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{natShiftL : ShiftL a Nat}} -> ShiftL (Frac a) Int
  ShiftL.semiringa (shiftLFrac {{semiRing = semiRing}}) = semiRingFrac {{semiRing = semiRing}}
  ShiftL.semiringb shiftLFrac = semiRingInt
  ShiftL.shiftl shiftLFrac x (pos n) = MkFrac (shiftl (num x) n) (den x) (denNotNull x)
  ShiftL.shiftl shiftLFrac x (negsuc n) = MkFrac (num x) (shiftl (den x) (suc n)) cheat
  ShiftL.shiftlProper shiftLFrac x x' (pos n) (pos .n) eqx refl = cheat 
  ShiftL.shiftlProper shiftLFrac _ _ (negsuc n) (negsuc .n) eqx refl = cheat
  ShiftL.shiftlNull shiftLFrac x = cheat
  ShiftL.shiftlSuc shiftLFrac x n = cheat
  {-# FOREIGN AGDA2HS
  instance ShiftL a Nat => ShiftL (Frac a) Int where
    shiftl x n
      | n >= 0     = MkFrac (shiftl (num x) n) (den x)
      | otherwise  = MkFrac (num x) (shiftl (den x) (negate n))
  #-}

-- Rational will be an alias for Frac Int.
Rational : Set
Rational = Frac Int
-- We won't compile this; we'll use Data.Ratio's Rational instead.

PosRational : Set
PosRational = Σ0 Rational (λ q -> null < q)
{-# COMPILE AGDA2HS PosRational #-}

-- Operations on positive rationals.
plusPos multPos : PosRational -> PosRational -> PosRational
plusPos (p :&: 0<p) (q :&: 0<q) = (p + q) :&: cheat
multPos (p :&: 0<p) (q :&: 0<q) = (p * q) :&: cheat
{-# COMPILE AGDA2HS plusPos #-}
{-# COMPILE AGDA2HS multPos #-}
halvePos : PosRational -> PosRational
halvePos (p :&: 0<p) = shiftl p (negsuc 0) :&: cheat
{-# COMPILE AGDA2HS halvePos #-}

-- The rationals are "a field containing ℤ that moreover can be embedded
-- into the field of fractions of ℤ".
-- So the abstract type class is defined like this:
record Rationals (a : Set) : Set₁ where
  field
    overlap {{decField}} : DecField a
    -- For any representation of integers, we can project a to a fraction of them.
    rationalsToFrac : {b : Set} {{integers : Integers b}} -> a -> Frac b
    @0 rationalsToFracInj : ∀ {b : Set} {{integers : Integers b}}
                               -> Injective {a} {Frac b} rationalsToFrac
    @0 rationalsToFracMor : ∀ {b : Set} {{integers : Integers b}}
                               -> SemiRingMorphism {a} {Frac b} rationalsToFrac
    @0 rationalsEmbedInts : ∀ {b : Set} {{integers : Integers b}}
                               -> Injective {b} {a} integersToRing
open Rationals {{...}} public
-- A similar problem here.
{-# FOREIGN AGDA2HS
class DecField a => Rationals a where
  rationalsToFrac :: Integers b => a -> Frac b
#-}
