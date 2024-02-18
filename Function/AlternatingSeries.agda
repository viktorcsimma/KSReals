-- A predicate showing
-- whether a Stream of AppRational will be an alternating series,
-- and the construction of their sum as a real.
-- (Later, we will prove that it is indeed the limit.)
{-# OPTIONS --erasure --guardedness #-}

module Function.AlternatingSeries where

open import Tool.Cheat

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int
open import Agda.Builtin.Unit
open import Haskell.Prim.Foldable using (foldr)
open import Haskell.Prim.List hiding (tail)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (itsTrue)

open import Algebra.Order
open import Algebra.SemiRing
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
open import Tool.ErasureProduct
open import Tool.Stream

{-# FOREIGN AGDA2HS
import Prelude (Integer, map)
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

-- Takes the parameters coiteStream takes
-- (a is the type of seeds).
-- See the conditions of O'Connor's Theorem 33.
@0 IsAlternating : {a : Set} {{ara : AppRational a}} -> Stream (Frac a) -> Set
IsAlternating xs = (∀ (i : Nat) -> abs (index xs (suc i)) < abs (index xs i))
                   × ((∀ (i : Nat) -> index xs i * index xs (suc i) < null)    -- is alternating
                   × (∀ (ε : PosRational) -> Σ0 Nat (λ n -> let fra = index xs n in
                                                      cast (num (abs fra)) ≤ cast (den (abs fra)) * (proj₁ ε))))
                                                        -- this ensures the limit is 0;
                                                        -- we only need one because
                                                        -- afterwards it's strictly decreasing

sumAlternatingStream : {a : Set} {{ara : AppRational a}} ->
                         (xs : Stream (Frac a)) -> @0 (IsAlternating xs) -> C a
sumAlternatingStream {a} xs hyp = MkC (rx xs) cheat
  where
  -- We have to specify `a` again;
  -- otherwise, Haskell believes it's a different type.
  rx : {a : Set} {{ara : AppRational a}} -> Stream (Frac a) -> PosRational -> a
  rx {a} xs ε = foldr _+_ null
                ( map (λ fa -> appDiv (num fa) (den fa) (denNotNull fa) divPrec)
                ( takeStream n xs))
    where
    logFloorε : Int
    logFloorε = ratLog2Floor (proj₁ ε) {proj₂ ε}
    -- See ARAlternatingSum.v.
    -- shift one logFloorε is an underestimate of ε.
    -- shift one (logFloorε - 1) is an underestimate of ε/2.
    -- And we need not perform the approximate division,
    -- since we can multiply the denominator
    -- with shift one (logFloorε - 1).
    -- And actually, this is equivalent
    -- to simply shifting the denominator.
    n : Nat
    n = proj₁ (countWhile
                 (λ _ fra ->
                   shift (abs (den fra)) (logFloorε + negsuc 0)
                     ≤# abs (num fra))
                 xs cheat)

    -- First we have to count them to calculate the required precision;
    -- then we have to iterate again, execute the divisions and sum the results.

    -- See Krebbers 5.1.
    -- Here is the plan.
    
    -- ε*31/16 is quick to calculate. (It must be something a bit smaller than 2ε.)
    -- Let underApp := appDiv (num (ε*15/16)) (div (ε*15/16)) (ratLog2Floor ε/32).
    -- Then:
    -- ε*29/32 ≤ underApp ≤ ε*31/32
    -- 0 < ε*29/64 ≤ underApp/2 ≤ ε*31/64 < ε/2
      -- Maybe this could be made even more precise.
    -- We then write an efficient comparison for dyadics.
    -- And then, we can use underApp/2 as the upper bound.
    -- One more thing: what about ε/2k?
    -- Its logarithm is largely OK; that is quick to compute.
    
    -- Then, an overapproximation of ε/2k.
    -- Let overApp = appDiv (num (ε*17/16)) (div (ε*17/16)) (ratLog2Floor ε/32)
    -- Then:
    -- ε*33/32 ≤ overApp ≤ ε*35/32
    -- ε/2 < ε*33/64 ≤ overApp/2 ≤ ε*35/64
    -- ε/2k ≤ overApp/2k = overApp * 2 ^ (-log₂ k - 1) ≤ overApp * 2 ^ (- natLog2Floor k - 1) =
    -- = shift overApp (- natLog2Floor k - 1)
      -- Here, k must not be zero.
      -- But - natLog2Floor (suc k) ≥ - natLog2Floor k - 1;
      -- so we can correct it this way.
    -- Let overAppp2k := shift overApp (- natLog2Floor (suc k)).
    -- And let appFra := appDiv nₖ dₖ (ratLog2Floor ε/2k).
      -- Here ratLog2Floor ε/2k ≥ ratLog2Floor ε - 1 - (1 + natLog2Floor k) =
      -- = ratLog2Floor ε - natLog2Floor k - 2.
      -- And we can freely put suc k there; we just increase the precision by that.
    -- Finally:
    -- |appFra + ε/2k| < ε/2
    -- it's enough to see that
    -- |appFra| + ε/2k < ε/2
    -- |appFra| < ε/2 - ε/2k
    -- , and it's enough to see that
    -- |appFra| < underApp/2 - overAppp2k
    -- |appFra| + overAppp2k < underApp/2
    -- And now, both sides are dyadics.
    -- They are both nonnegative, and the left side converges to zero;
    -- so there will be a k for which the predicate is false.
    {-
    logFloorε : Int
    logFloorε = ratLog2Floor (proj₁ ε) {proj₂ ε}
    underApp : {a : Set} {{ara : AppRational a}} -> a
    underApp = let mulε = proj₁ (multPos ε (MkFrac (pos 15) (pos 16) tt :&: itsTrue)) in
           appDiv (cast (num mulε)) (cast (den mulε)) cheat (logFloorε + (negsuc 4))
    overApp : {a : Set} {{ara : AppRational a}} -> a
    overApp = let mulε = proj₁ (multPos ε (MkFrac (pos 17) (pos 16) tt :&: itsTrue)) in
           appDiv (cast (num mulε)) (cast (den mulε)) cheat (logFloorε + (negsuc 4))
    n : Nat
    n = proj₁ (countWhile (λ k fra -> let appFra = appDiv (num fra) (den fra) (denNotNull fra) (logFloorε - pos (natLog2Floor (suc k)) + negsuc 1); overAppp2k = shift overApp (negate (pos (natLog2Floor (suc k))))
                                      in shift underApp (negsuc 0)
                                           ≤# abs appFra + overAppp2k)
                          xs
                          cheat)
    -}
    {-
    n = proj₁ (countWhile (λ k fra -> proj₁ (halvePos ε) ≤# testBound k fra)
                          (tail xs) -- we start from one because of the denominator
                          cheat
                          1) -- the starting index
       where
       εp2k : Nat -> PosRational
       εp2k k = multPos ε (MkFrac (pos 1) (pos (shiftl k 1)) cheat :&: itsTrue)
       testBound : {a : Set} {{ara : AppRational a}} -> Nat -> Frac a -> Rational
       testBound {a} k fra = abs (cast {a} {Rational}
                                    (appDiv (num fra) (den fra) (denNotNull fra)
                                       ((pos 1) + (ratLog2Floor (proj₁ (εp2k k)) {proj₂ (εp2k k)})))
                                  + proj₁ (εp2k k))
    -}
    divPrec : Int
    divPrec = logFloorε + negsuc 0 + negsuc (natLog2Floor (suc n))
    -- natLog2Floor would round it in the wrong direction
    -- and suc n is needed for the sake of the logarithm
    -- divPrec = ratLog2Floor (proj₁ (halvePos ε) * MkFrac (pos 1) (pos (suc n)) tt) {cheat}
{-# COMPILE AGDA2HS sumAlternatingStream #-}

