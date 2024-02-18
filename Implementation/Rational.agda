-- An implementation of the rationals
-- as fractions of integers.
{-# OPTIONS --erasure #-}

module Implementation.Rational where

{-# FOREIGN AGDA2HS {-# LANGUAGE MultiParamTypeClasses #-}

import qualified Prelude
import Prelude (Integer, Bool, otherwise, fromIntegral, ($), (&&), (||))

import Algebra.Field
import Operator.Cast
import Implementation.Nat
import Implementation.Int

#-}

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim using (⊥; id; if_then_else_)

open import Tool.ErasureProduct
import Implementation.Nat as Nat
open import Implementation.Int
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Order
open import Operator.Decidable
open import Operator.Abs
open import Operator.Cast
open import Operator.ShiftL
open import Operator.Shift

open import Implementation.Frac

-- Rational will be an alias for Frac Int.
Rational : Set
Rational = Frac Int
-- We won't compile this; we'll use Data.Ratio's Rational instead.
-- Or can we? We haven't written the instances for it...
-- But Data.Ratio would mean a performance boost.
{-# COMPILE AGDA2HS Rational #-}

truncate ceil floor : Rational -> Int
truncate q = intQuot (num q) (den q) (denNotNull q)
ceil q = if (intRem (num q) (den q) (denNotNull q) ≃# (pos zero))
         then truncate q else truncate q + (if q <# null then negsuc 0 else pos 0)
floor q = if (intRem (num q) (den q) (denNotNull q) ≃# (pos zero))
         then truncate q else truncate q + (if q <# null then pos 0 else pos 1)
{-# FOREIGN AGDA2HS
-- quot rounds towards zero, div towards minus infinity.
ceil :: Rational -> Integer
ceil q = num q `Prelude.div` den q
floor :: Rational -> Integer
-- maybe this can be solved better
floor q = if (num q `Prelude.mod` den q Prelude.== 0) then ceil q else ceil q + 1
#-}
-- TODO: correctness proofs for them

-- This returns the floor of the logarithm.
ratLog2Floor : (q : Rational) -> @0 {null < q} -> Int
ratLog2Floor q = pos (Nat.natLog2Floor (natAbs (num q)) {cheat})
                    + negate (pos (Nat.natLog2Floor (natAbs (den q)) {cheat}))
{-# COMPILE AGDA2HS ratLog2Floor #-}

PosRational : Set
PosRational = Σ0 Rational (λ q -> null < q)
{-# COMPILE AGDA2HS PosRational #-}

-- Operator on positive rationals.
plusPos multPos : PosRational -> PosRational -> PosRational
plusPos (p :&: 0<p) (q :&: 0<q) = (p + q) :&: cheat
multPos (p :&: 0<p) (q :&: 0<q) = (p * q) :&: cheat
{-# COMPILE AGDA2HS plusPos #-}
{-# COMPILE AGDA2HS multPos #-}
halvePos : PosRational -> PosRational
halvePos (p :&: 0<p) = shift p (negsuc 0) :&: cheat
{-# COMPILE AGDA2HS halvePos #-}

{-
-- we don't need this for now.

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
-}
