-- The exponentiation function;
-- built by first defining it
-- on AppRationals in [-1,0],
-- then on all AppRationals;
-- and lifting this function.
{-# OPTIONS --erasure #-}

module Function.Exp where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, const)

import Implementations.Int
#-}

open import Tools.Cheat

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Tools.ErasureProduct
open import Algebra.Ring
open import Algebra.Field
open import Algebra.MetricSpace
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
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

open import Haskell.Prim using (if_then_else_; const; itsTrue)

-- NOTE: this only works for -1≤x≤0.
-- Now, we only define it for "rational" parameters.
{-# TERMINATING #-}
smallExpQ : ∀ {a : Set} {{ara : AppRationals a}}
         -> Σ0 a (IsIn [ negate one , null ]) -> C a
smallExpQ {a} (x :&: _) = MkC (λ ε -> smallExpHelper 0 1 (firstPrec ε) one null (halvePos ε) x) cheat
  where
  -- The trick is that we actually do it with a precision of ε/2,
  -- but the appDivs' precision will be ε/4, ε/8, ε/16 etc.
  -- This gives the precision ε.
  firstPrec : PosRational -> Int
  firstPrec ε = ratLog2Floor (proj₁ (halvePos (halvePos ε))) {proj₂ (halvePos (halvePos ε))}

  -- the index of the step (k),
  -- k!,
  -- the actual precision,
  -- xᵏ,
  -- and the one where the result is going to be
  smallExpHelper : ∀ {a : Set} {{ara : AppRationals a}}
         -> (k fact : Nat) (divPrec : Int) (powxk res : a) (ε : PosRational) (x : a) -> a
  smallExpHelper {a} k fact divPrec powxk res ε x =
    if abs (nextFrac powxk) ≤# proj₁ ε   -- that's why it only works for -1≤x≤0; it uses the alternating series theorem
      then res                           -- (see O'Connor for details)
      else smallExpHelper
            (1 + k)
            (fact * (1 + k))
            (divPrec - pos 1)
            (powxk * x)
            (res + aNextFrac fact powxk divPrec)
            ε x
    where
    -- Here, the constraints for type a have to be defined again;
    -- because Haskell thinks it's a different type.
    nextFrac : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                 -> a -> Rational
    nextFrac {a} powxk = cast {a} {Rational} powxk * MkFrac (pos 1) (pos fact) cheat

    -- Here, we would have to calculate appDiv with a precision of 2^divPrec/powxk
    -- to have a 2^divPrec precision after the multiplication.
    -- But if -1≤x≤0, it doesn't matter (and the logarithm is even dangerous).
    aNextFrac : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
                 -> (fact : Nat) (powxk : a) (divPrec : Int) -> a
    aNextFrac {a} fact powxk divPrec
      = powxk * appDiv one (cast {Int} {a} (pos fact)) cheat divPrec
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
