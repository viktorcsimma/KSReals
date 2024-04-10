-- A predicate showing
-- whether a Stream of AppRational will be an alternating series,
-- and the construction of their sum as a real.
-- (Later, we will prove that it is indeed the limit.)
{-# OPTIONS --erasure --guardedness #-}

module Function.AlternatingSeries where

open import Tool.Cheat

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int
open import Agda.Builtin.Unit
open import Haskell.Prim.Foldable using (foldr)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (IsTrue; itsTrue)

open import Algebra.Order
open import Algebra.SemiRing
open import Algebra.Ring
open import Implementation.Nat using (natLog2Floor)
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Operator.Abs
open import Operator.Cast
open import Operator.Decidable
open import Operator.Shift
open import RealTheory.AppRational
open import RealTheory.Completion
open import RealTheory.MetricSpace
open import Tool.ErasureProduct
open import Tool.Stream
open import Tool.Witness

{-# FOREIGN AGDA2HS
import Prelude (Bool, Integer, error, otherwise)
import Implementation.Nat
import Implementation.Int
#-}

-- From CoRN (reals/faster/ARAlternatingSum.v):
{-
The goal of this section is to compute the infinite alternating sum. Since
we do not have a precise division operation, we want to postpone divisions as
long as possible. Hence we parametrize our infinite sum by a stream [sN]
of numerators and a stream [sD] of denominators.

To compute an infinite series at precision epsilon, the finite number n of
terms to sum can be computed exactly, because sN n / sD n < epsilon/2 is
equivalent to sN n < (sD n) * epsilon/2, which does not involve the approximate
division. In the other epsilon/2, we can approximate the n divisions at
precision 2^k such as n*2^k < epsilon/2.
-}

-- We will use Frac a here, where a is an AppRational type.
-- This way, we can have only one stream and ensure
-- the denominator is not zero.

-- We define this that way because
-- we will need exactly this function
-- in sumAlternatingStream.
-- See 5.1 at K&S and the version below it.
-- This also reduces complexity
-- but requires the user to give a correct function
-- for every stream;
-- unerasably.
thatNearToZero : {a : Set} {{ara : AppRational a}} -> Frac a -> PosRational -> Nat -> Bool
thatNearToZero xk ε k = let prec = ratLog2Floor (proj₁ ε) {proj₂ ε} + negsuc k in
                          -- We put it with IsTrue;
                          -- we already require for an AppRational type
                          -- that this should be equivalent to ball.
                          cast (abs (appDiv (num xk) (den xk) (denNotNull xk)
                                             prec)
                                + shift one prec)
                          ≤# proj₁ (halvePos ε)
                          {-
                          ball (halvePos ε)
                               (appDiv (num xk) (den xk) (denNotNull xk)
                                     prec
                                 + shift one prec)
                               null)
                          -}
{-# COMPILE AGDA2HS thatNearToZero #-}
HasThatNearToZero : {a : Set} {{ara : AppRational a}} -> Stream (Frac a) -> Set
HasThatNearToZero xs = ∀ (ε : PosRational) -> Σ0 Nat (λ k -> IsTrue (thatNearToZero (index xs k) ε k))
{-# COMPILE AGDA2HS HasThatNearToZero #-}
-- TODO: a non-erased proof that all series converging to zero have this property.

-- Automatically calculates the least eligible index for a series
-- if we already have an erased proof of the fact that such an index exists.
-- Uses the witness function.
-- Good for cases where you can prove the existence but with rough overapproximations.
-- (And for cheating away the proofs...)
autoHasThatNearToZero : {a : Set} {{ara : AppRational a}} (xs : Stream (Frac a)) -> @0 (HasThatNearToZero xs) -> HasThatNearToZero xs
autoHasThatNearToZero xs hyp ε = witness (λ k -> thatNearToZero (index xs k) ε k) (hyp ε)
{-# FOREIGN AGDA2HS
-- The Agda definition would be quite slow:
-- it would calculate index xs 0, then index xs 1 seperately, then index xs 2...
-- so it would be O(n^2).
-- Instead, we do it with the tools of Prelude:
autoHasThatNearToZero :: AppRational a => Stream (Frac a) -> HasThatNearToZero xs
autoHasThatNearToZero xs ε = go xs ε 0
  where
  go :: AppRational a => Stream (Frac a) -> PosRational -> Natural -> Σ0 Natural
  go [] _ _ = error "Stream cannot be finite"
  go (x:xs) ε k
    | thatNearToZero x ε k = (:&:) k
    | otherwise = go xs ε (1+k)
#-}

-- we will need a tuple here
IsAlternating : {a : Set} {{ara : AppRational a}} -> Stream (Frac a) -> Set
IsAlternating xs = Tuple0 (HasThatNearToZero xs)
                   ( (∀ (i : Nat) -> abs (index xs (suc i)) < abs (index xs i))  -- decreasing
                   × (∀ (i : Nat) -> index xs i * index xs (suc i) < null) )     -- alternating
{-# COMPILE AGDA2HS IsAlternating #-}

-- The sum of the first n elements of a stream.
partialSum : ∀{a : Set}{{semiring : SemiRing a}} -> Stream a -> Nat -> a
partialSum = partialFoldr _+_ null
{-# COMPILE AGDA2HS partialSum #-}

-- The sum of an infinite alternating series
-- as a real.
-- The idea is that at an ε approximation,
-- we only count until the index
-- that the function in HasThatNearToZero gives for ε.
-- See 5.1 at K&S.
sumAlternatingStream : {a : Set} {{ara : AppRational a}} ->
                         (xs : Stream (Frac a)) -> IsAlternating xs -> C a
sumAlternatingStream xs (anyNear :&: (dec , alt)) =
  MkC
    (λ ε -> let km1 = proj₁ (anyNear ε); k = suc km1; divPrec = ratLog2Floor (proj₁ ε) {cheat} + negsuc k in
           partialSum (map (λ {(MkFrac n d dNotNull) -> appDiv n d dNotNull divPrec}) xs) k
    )
    cheat
{-# COMPILE AGDA2HS sumAlternatingStream #-}
