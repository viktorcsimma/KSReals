-- A predicate showing
-- whether a Stream of AppRationals will be an alternating series,
-- and the construction of their sum as a real.
-- (Later, we will prove that it is indeed the limit.)
{-# OPTIONS --erasure --guardedness #-}

module Functions.AlternatingSeries where

open import Tools.Cheat

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int
open import Agda.Builtin.Unit
open import Haskell.Prim.Foldable using (foldr)
open import Haskell.Prim.List
open import Haskell.Prim.Tuple

open import Algebra.Order
open import Algebra.Ring
open import Implementations.Int
open import Implementations.Rational
open import Operations.Abs
open import Operations.Cast
open import Operations.Decidable
open import RealTheory.AppRationals
open import RealTheory.Completion
open import Tools.ErasureProduct
open import Tools.Stream

{-# FOREIGN AGDA2HS
import Prelude (Integer, map)
import Implementations.Nat
import Implementations.Int
#-}

-- From CoRN:
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

-- Takes the parameters coiteStream takes
-- (a is the type of seeds).
-- See the conditions of O'Connor's Theorem 33.
@0 IsAlternating : {a : Set} {{ara : AppRationals a}} -> Stream (Frac a) -> Set
IsAlternating xs = (∀ (i : Nat) -> abs (index xs (suc i)) < abs (index xs i))
                   × ((∀ (i : Nat) -> index xs i * index xs (suc i) < null)    -- is alternating
                   × (∀ (ε : PosRational) -> Σ0 Nat (λ n -> let fra = index xs n in
                                                      cast (num (abs fra)) ≤ cast (den (abs fra)) * (proj₁ ε))))
                                                        -- this ensures the limit is 0;
                                                        -- we only need one because
                                                        -- afterwards it's strictly decreasing

sumAlternatingStream : {a : Set} {{ara : AppRationals a}} ->
                         (xs : Stream (Frac a)) -> @0 (IsAlternating xs) -> C a
sumAlternatingStream {a} xs hyp = MkC (rx xs) cheat
  where
  -- We have to specify `a` again;
  -- otherwise, Haskell believes it's a different type.
  rx : {a : Set} {{ara : AppRationals a}} -> Stream (Frac a) -> PosRational -> a
  rx xs ε = foldr _+_ null
            ( map (λ fa -> appDiv (num fa) (den fa) (denNotNull fa) divPrec)
            ( takeStream n xs))
    where
    -- First we have to count them to calculate the required precision;
    -- then we have to iterate again, execute the divisions and sum the results.
    n : Nat
    n = proj₁ (countWhile (λ fra -> cast (den (abs fra)) * (proj₁ (halvePos ε)) <# cast (num (abs fra))) xs (proj₁ (snd (snd hyp) (halvePos ε)) :&: cheat))
    -- "...we can approximate the n divisions at precision 2^k such as n*2^k < epsilon/2."
    -- For now, we'll divide by suc n so as to be sure that n is not zero.
    divPrec : Int
    divPrec = ratLog2Floor (proj₁ (halvePos ε) * MkFrac (pos 1) (pos (suc n)) tt) {cheat}
{-# COMPILE AGDA2HS sumAlternatingStream #-}
