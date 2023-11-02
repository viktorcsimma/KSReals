-- Implementing trigonometric functions
-- based on their power series
-- (which will be shown to be alternating series
-- on an appropriate interval).
-- The definition of π can also be found here.
{-# OPTIONS --erasure --guardedness #-}

module Functions.Trigonometric where

open import Tools.Cheat

open import Agda.Builtin.Nat hiding (_+_; _-_; _*_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (id)

open import Algebra.Ring
open import Functions.AlternatingSeries
open import Implementations.Nat
open import Implementations.Rational
open import Operations.Abs
open import Operations.Cast
open import Operations.ShiftL
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Interval
open import RealTheory.Reals
open import Tools.ErasureProduct
open import Tools.Stream

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (id)
import Implementations.Nat
import Implementations.Int
import RealTheory.Reals
#-}

-- TODO: this does not terminate for x=1 and x=-1
-- Now, let's just do it for -1/2≤x≤1/2. (It may even be quicker this way.)

-- Now, we only define it for "rational" parameters.
-- But first for a fraction of AppRationals
-- (this will be needed for 1 / 57 etc. in the definition of π).
-- Σ(-1)ⁱ*x²ⁱ⁺¹/(2i+1)
smallArcTgFracQ : ∀ {a : Set} {{ara : AppRationals a}}
             -> Σ0 (Frac a {{Ring.super ring}})
                (IsIn [ MkFrac (shift (negate one) (negsuc 0)) one cheat ,
                        MkFrac (shift one (negsuc 0)) one cheat ])
             -> C a
-- The seed is going to be a tuple
-- containing the index of the step (starting from zero)
-- and the current value of (-1)^i * x^(2i+1).
smallArcTgFracQ {a} (x :&: _) = sumAlternatingStream
                            (coiteStream
                               (λ {(i , pow) -> pow * MkFrac one (cast (pos (suc (2 * i)))) cheat})
                               (λ {(i , pow) -> suc i , negate (x * x * pow)})
                               (0 , x))
                               cheat
{-# COMPILE AGDA2HS smallArcTgFracQ #-}

-- And now a formula for π; using smallArcTgFracQ.
-- See Krebbers and Spitters.
pi : ∀ {a : Set} {{ara : AppRationals a}} -> C a
pi = returnC (cast (pos 176)) * smallArcTgFracQ (MkFrac one (cast (pos 57)) cheat :&: cheat)
    + (returnC (cast (pos 28)) * smallArcTgFracQ (MkFrac one (cast (pos 239)) cheat :&: cheat))
    - (returnC (cast (pos 48)) * smallArcTgFracQ (MkFrac one (cast (pos 682)) cheat :&: cheat))
    + returnC (cast (pos 96)) * smallArcTgFracQ (MkFrac one (cast (pos 12943)) cheat :&: cheat)
{-# COMPILE AGDA2HS pi #-}
