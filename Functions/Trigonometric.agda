-- Implementing trigonometric functions
-- based on their power series
-- (which will be shown to be alternating series
-- on an appropriate interval).
-- The definition of π can also be found here.
{-# OPTIONS --erasure --guardedness #-}

module Functions.Trigonometric where

open import Tools.Cheat

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_+_; _-_; _*_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Unit
open import Haskell.Prim.Bool
open import Haskell.Prim.Tuple
open import Haskell.Prim using (id; if_then_else_; itsTrue)

open import Algebra.Field using (recip)
import Algebra.MetricSpace
open import Algebra.Ring
open import Functions.AlternatingSeries
open import Implementations.Nat
import Implementations.Int
open import Implementations.Rational
open import Operations.Abs
open import Operations.Cast
open import Operations.Decidable
open import Operations.Pow
open import Operations.ShiftL
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Continuity
import RealTheory.Instances.Pow
open import RealTheory.Interval
open import RealTheory.Reals
open import Tools.ErasureProduct
open import Tools.Stream

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (id, snd, (&&))
import Implementations.Nat
import Implementations.Int
import RealTheory.Instances.Pow
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
pi = returnC (cast (pos 176)) * compress (smallArcTgFracQ (MkFrac one (cast (pos 57)) cheat :&: cheat))
    + (returnC (cast (pos 28)) * compress (smallArcTgFracQ (MkFrac one (cast (pos 239)) cheat :&: cheat)))
    - (returnC (cast (pos 48)) * compress (smallArcTgFracQ (MkFrac one (cast (pos 682)) cheat :&: cheat)))
    + returnC (cast (pos 96)) * compress (smallArcTgFracQ (MkFrac one (cast (pos 12943)) cheat :&: cheat))
{-# COMPILE AGDA2HS pi #-}

{-
arcTgFracQ : ∀ {a : Set} {{ara : AppRationals a}}
             -> Σ0 (Frac a {{Ring.super ring}})
             -> C a
arcTgFrac
-}

-- sin, cos and arctg are uniformly continuous with moduli id.
-- ucFunArcTgQ : 

-- Σ(-1)ⁱ*x²ⁱ⁺¹/(2i+1)!
smallSinFracQ : ∀ {a : Set} {{ara : AppRationals a}}
             -> Σ0 (Frac a {{Ring.super ring}})
                (IsIn [ MkFrac (shift (negate one) (negsuc 0)) one cheat ,     -- [1/2, 1/2]
                        MkFrac (shift one (negsuc 0)) one cheat ])
             -> C a
-- The seed is going to be a tuple
-- containing the index of the step (starting from one)
-- and the value of (-1)^(i-1) * x^(2i-1) / (2i-1)!
-- (so the previous member of the sum).
smallSinFracQ {a} (x :&: _) = sumAlternatingStream
                            (coiteStream
                               snd
                               (λ {(i , fra) -> suc i ,
                                                negate (MkFrac one (cast (pos (2 * i * suc (2 * i)))) cheat) * x * x * fra})
                               (1 , x))
                               cheat
{-# COMPILE AGDA2HS smallSinFracQ #-}

-- Now for any Frac a.
-- We'll use the equality
-- sin(x) = 3sin(x/3) - 4sin³(x/3).
{-# TERMINATING #-}
sinFracQ : ∀ {a : Set} {{ara : AppRationals a}}
             -> Frac a {{Ring.super ring}}
             -> C a
sinFracQ x =    -- K&S recommend 2^(-75) as an upper bound for high-precision calculations.
                -- See p. 21.
                 -- if (abs x ≤# MkFrac (shift one (negsuc 74)) one cheat)
                 if (abs (num x) ≤# shift (abs (den x)) (negsuc 74))
                 then smallSinFracQ (x :&: cheat)
                 else raise (sinFracQ (MkFrac (num x) (cast 3 * den x) cheat))
  where
  raise : ∀ {a : Set} {{ara : AppRationals a}} -> C a -> C a
  raise s = mapC (prefixCon
                    (λ s -> s * (cast 3 - shiftl (s ^ fromInteger 2) 2))
                    (WrapMod (λ ε -> multPos ε (MkFrac (pos 1) (pos 9) tt :&: itsTrue))
                                                         -- sin(x/3) ∈ [-1,1];
                                                         -- so the derivative is at most 9
                                                         -- see Krebbers' DReal.hs
                             cheat))
                 (compress s)
{-# COMPILE AGDA2HS sinFracQ #-}

-- Now specially for simply a.
sinQ : ∀ {a : Set} {{ara : AppRationals a}}
             -> a -> C a
sinQ x = sinFracQ (MkFrac x one cheat)
{-# COMPILE AGDA2HS sinQ #-}

-- Here, the modulus of continuity is simply id.
sinQUc : ∀ {a : Set} {{ara : AppRationals a}}
             -> UcFun a (C a)
sinQUc = prefixCon sinQ (WrapMod id cheat)
{-# COMPILE AGDA2HS sinQUc #-}

-- And finally:
sin : ∀ {a : Set} {{ara : AppRationals a}}
         -> (x : C a) -> C a
sin x = proj₁' (bindC sinQUc) (compress x)
{-# COMPILE AGDA2HS sin #-}
