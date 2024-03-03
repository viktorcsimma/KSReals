-- An efficient implementation of the square root function,
-- based on Newton iterations.
{-# OPTIONS --erasure --guardedness #-}

module Function.SquareRoot where

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Bool
open import Haskell.Prim.Tuple
open import Haskell.Prim using (if_then_else_)

open import Algebra.Setoid
open import Algebra.Order
open import Algebra.SemiRing
open import Algebra.Ring
open import Function.Exp using (exp)
open import Implementation.Nat using (natLog2Floor)
open import Implementation.Int using (natAbs; intRem)
open import Implementation.Frac
open import Implementation.Rational
open import Operator.Decidable
open import Operator.ShiftL
open import Operator.Shift
open import RealTheory.AppRational
open import RealTheory.Completion
open import RealTheory.Interval
open import RealTheory.Real using (compress)
open import RealTheory.Continuity
open import Tool.ErasureProduct

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (snd, (&&), Integer)

import Implementation.Nat (suc)
import Implementation.Int (pos, negsuc)
import RealTheory.Real
#-}

-- We'll need this later.
applyNTimes : ∀ {a : Set} -> Nat -> (a -> a) -> a -> a
applyNTimes zero _ x = x
applyNTimes (suc n) f x = applyNTimes n f (f x)
{-# FOREIGN AGDA2HS
applyNTimes :: Natural -> (a -> a) -> a -> a
applyNTimes 0 _ x = x
applyNTimes n f x = applyNTimes (n Prelude.- 1) f (f x)
#-}

-- But how do you handle the sign?
-- There might be positive reals which have negative approximations... hm.
-- Let's cheat for now.

-- One step.
-- See O'Connor p. 13.
-- i is the index of the step,
-- x is the number we want the square root of
-- and b is the i'th approximation.
-- bᵢ₊₁ := (bᵢ + x / bᵢ) / 2
-- Since the final /2 can be exact,
-- appDiv only needs a 2^(-2ⁱ⁺¹) precision.
sqrtQStep : ∀ {a : Set} {{ara : AppRational a}}
                 -> Nat -> (x b : a) -> a
sqrtQStep i x b = shift
                    (b + appDiv x b cheat
                          (shiftl (negsuc 0) (suc i)))
                    (negsuc 0)
{-# COMPILE AGDA2HS sqrtQStep #-}

-- And this is going to give a regular function:
-- "n is the first natural number
-- such that 2^(-2ⁿ)≤ε."
-- Rewritten:
-- -2ⁿ ≤ log₂ ε
-- 2ⁿ ≥ - log₂ ε
-- n ≥ log₂ (- log₂ ε) -- here, a suc is needed because of flooring
-- But for this, we have to assume ε ≤ 1.
-- Otherwise, n := 0 is enough.
smallSqrtQ : ∀ {a : Set} {{ara : AppRational a}}
           -> Σ0 a (λ x -> IsIn [ one , shiftl one 2 [ x) -> C a
                                     -- ^ we need 4 here as the upper bound
                                     -- because we have to multiply x with 4s later
                                     -- until it gets into the interval
smallSqrtQ (x :&: _) = MkC (go x) cheat
  where
  go : ∀ {a : Set} {{ara : AppRational a}}
          -> a -> PosRational -> a
  go x ε = snd (applyNTimes n (step x) (1 , (shift (one + x) (negsuc 0))))
    where
    n : Nat
    n = if (one <# (proj₁ ε))
        then 0
        else suc (natLog2Floor (natAbs (ratLog2Floor (proj₁ ε) {proj₂ ε})) {cheat})

    -- The tuple will store the index of the coming step.
    -- So it looks like (suc i , bᵢ).
    -- That's why we start from 1.
    step : ∀ {a : Set} {{ara : AppRational a}}
            -> a -> (Nat × a) -> (Nat × a)
    step x (i , b) = (suc i , sqrtQStep i x b)
{-# COMPILE AGDA2HS smallSqrtQ #-}

-- The formula is
-- "sqrt(4ᵐ * x) / 2ᵐ
-- (where m is some integer such that 1 ≤ 4ᵐx < 4)."
-- This means:
-- 0 ≤ 2*m + log₂ x < 2
-- -2*m ≤ log₂ x < -2*m + 2
-- log₂ x - 2 < -2*m ≤ log₂ x
-- - log₂ x ≤ 2*m < 2 - log₂ x
-- then:
-- log₂ x ≥ log2Floor x
-- - log₂ x ≤ - log2Floor x
-- 2 - log₂ x ≤ 2 - log2Floor x
-- this means  2*m < 2 - log2Floor x
-- so 2*m shall be 1 - log2Floor x or - log2Floor x,
-- whichever is even
sqrtQ : ∀ {a : Set} {{ara : AppRational a}}
           -> Σ0 a (λ x -> null ≤ x) -> C a
sqrtQ (x :&: _) = if x ≃# null then returnC null
                     -- this branch is covered in the last one
                     -- else if one ≤# x && x <# shiftl one 2 then smallSqrtQ (x :&: cheat)
                     else smallSqrtQ (shift x twom :&: cheat) * returnC (shift one (negate m))
  where
  logx twom m : Int
  logx = log2Floor x cheat
  twom = if intRem logx (pos 2) tt ≃# pos 0    -- as I see, the even function of Haskell works like this
         then negate logx
         else pos 1 + negate logx
  m = shift twom (negsuc 0)
{-# COMPILE AGDA2HS sqrtQ #-}

sqrtQUc : ∀ {a : Set} {{ara : AppRational a}}
           -> UcFun (Σ0 a (λ x -> null ≤ x)) (C a)
sqrtQUc = sqrtQ :^: WrapMod (λ ε -> multPos ε ε) cheat
{-# COMPILE AGDA2HS sqrtQUc #-}

-- And here,
-- if we know that 0 ≤ x,
-- we simply swap all negative approximations
-- to 0.
sqrt : ∀ {a : Set} {{ara : AppRational a}}
           -> (x : C a) -> @0 (null ≤ x) -> C a
sqrt {a} x 0≤x = proj₁' (bindC {{psa = prelengthInterval {a} {[ null ,+∞[}}} sqrtQUc)
                     (MkC (λ ε -> let xε = fun (compress x) ε in
                                   if (xε <# null) then null :&: cheat
                                   else xε :&: cheat)
                          cheat)
{-# COMPILE AGDA2HS sqrt #-}

-- A correctness proof:
{-
@0 sqrtIsCorrect : ∀ {a : Set} {{ara : AppRational a}}
                   -> (x : C a) -> sqrt x * sqrt x ≃ x
sqrtIsCorrect = cheat
-}

-- And an ultimate proof that could once be realised:
{-
@0 sqrtIsExpHalf : ∀ {a : Set} {{ara : AppRational a}}
                   -> (x : C a) -> sqrt x ≃ exp (1/2 * ln x)
sqrtIsExpHalf = cheat
-}
