-- The exponentiation function;
-- built by first defining it
-- on AppRationals in [-1,0],
-- then on all AppRationals;
-- and lifting this function.
{-# OPTIONS --erasure --guardedness #-}

module Functions.Exp where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, const, snd)

import Implementations.Nat
import Implementations.Int
#-}

open import Tools.Cheat

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Tuple

open import Tools.ErasureProduct
open import Tools.Stream
open import Algebra.Ring
open import Algebra.Field
open import Algebra.MetricSpace
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
open import Functions.AlternatingSeries
open import Operations.Abs
open import Operations.Decidable
open import Operations.Cast
open import Operations.Pow
open import Operations.ShiftL
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Continuity
open import RealTheory.Reals
open import RealTheory.Interval

open import Haskell.Prim using (if_then_else_; const; itsTrue; id)

-- This only works for -1≤x≤0 (that's when it is an alternating sum).
-- Now, we only define it for "rational" parameters.
-- Σxⁱ/i!
smallExpQ : ∀ {a : Set} {{ara : AppRationals a}}
         -> Σ0 a (IsIn [ negate one , null ]) -> C a
-- The seed is going to be a Nat × Frac a tuple,
-- containing the index of the step (starting from 1) and the previous fraction.
smallExpQ {a} (x :&: _) = sumAlternatingStream
                            (coiteStream snd (λ {(n , fra) -> suc n , MkFrac (num fra * x) (den fra * cast (pos n)) cheat}) (1 , one))
                            cheat
{-# COMPILE AGDA2HS smallExpQ #-}

e : ∀ {a : Set} {{ara : AppRationals a}}
       -> C a
e = recip (smallExpQ (negate one :&: cheat)) cheat
{-# COMPILE AGDA2HS e #-}

smallExpQUc : ∀ {a : Set} {{ara : AppRationals a}}
                -> UcFun (Σ0 a (IsIn [ negate one , null ])) (C a)
-- The modulus can be approximated from above
-- by the largest derivative on the interval;
-- which is e^0 = 1.
smallExpQUc = smallExpQ :^: WrapMod (const (one :&: itsTrue)) cheat
{-# COMPILE AGDA2HS smallExpQUc #-}

-- And now, we expand it to reals.
smallExp : ∀ {a : Set} {{ara : AppRationals a}}
                -> UcFun (C (Σ0 a (IsIn [ negate one , null ]))) (C a)
smallExp = bindC {{prelengthInterval {I = [ negate one , null ]}}} smallExpQUc
{-# COMPILE AGDA2HS smallExp #-}

-- From Krebbers and Spitters:
{-
The series described in this section converge faster for arguments closer to 0. We use
Equation 5.2 and 5.4 repeatedly to reduce the input to a value |x| ∈ [0, 2 k ). For 50 ≤ k,
this yields nearly always major performance improvements, for higher precisions setting it
to 75 ≤ k yields even better results.
-}
-- Maybe we should use that somehow.

-- Now for any rational parameter.
{-# TERMINATING #-}
expQ : ∀ {a : Set} {{ara : AppRationals a}}
         -> (x : a) -> C a
expQ x = if (null <# x) then recip (expQ (negate x)) cheat
         else (if (x <# negate one) then
           (let exp2 = expQ (shift x (negsuc 0)) in exp2 * exp2)
         else smallExpQ (x :&: cheat))
{-# COMPILE AGDA2HS expQ #-}

-- O'Connor's idea is that
-- expQ is uniformly continuous on any ]-∞,upperBound], where upperBound ∈ ℤ.
-- And then, for any real, upperBound will simply be the canonical bound.
expQUc :  ∀ {a : Set} {{ara : AppRationals a}}
           -> (upperBound : Int)
           -> UcFun (Σ0 a (IsIn ]-∞, cast upperBound ])) (C a)
expQUc upperBound = prefixCon  -- actually, this is _:^:_, but this helps agda2hs
                    (λ x -> expQ (proj₁ x))
                      (if upperBound ≤# null
                      then WrapMod (λ ε -> (proj₁ ε) * shift one (negate upperBound) --ε*2⁻ᵘᴮ
                                                   :&: cheat) cheat
                      else WrapMod (λ ε -> (proj₁ ε) * MkFrac one (pos (hsFromIntegral 3 ^ natAbs upperBound)) cheat
                                                   --ε*3⁻ᵘᴮ
                                                   :&: cheat) cheat)
{-# COMPILE AGDA2HS expQUc #-}

-- And now, let's extend it.
exp : ∀ {a : Set} {{ara : AppRationals a}}
         -> (x : C a) -> C a
exp x = proj₁' (bindC {{prelengthInterval {I = ]-∞, cast (canonicalBound x) ]}}}
          (expQUc (canonicalBound x))) (MkC (λ ε -> fun x ε :&: cheat) cheat)
        -- ^ this is simply x cast to C (Σ0 etc.)
{-# COMPILE AGDA2HS exp #-}
