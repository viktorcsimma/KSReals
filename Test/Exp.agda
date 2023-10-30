-- A module for testing the library
-- with an unverified version
-- of the exponentiation function.
{-# OPTIONS --erasure #-}

module Test.Exp where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer)

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
open import Operations.Decidable
open import Operations.Cast
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Reals
open import RealTheory.Interval

open import Haskell.Prim using (if_then_else_)

-- NOTE: this only works for -1≤x≤0.
-- Now, we only define it for "rational" parameters.
{-# TERMINATING #-}
smallExp : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
         -> (x : a) -> @0 IsIn [ negate one , null ] x -> C a
smallExp {a} x _ = MkC (λ ε -> smallExpHelper 0 1 (firstPrec ε) one null (halvePos ε) x) cheat
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
  smallExpHelper : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
         -> (k fact : Nat) (divPrec : Int) (powxk res : a) (ε : PosRational) (x : a) -> a
  smallExpHelper {a} k fact divPrec powxk res ε x =
    if (nextFrac powxk) ≤# proj₁ ε   -- that's why it only works for -1≤x≤0
      then res
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
{-# COMPILE AGDA2HS smallExp #-}

e : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
       -> C a
e = smallExp one cheat
{-# COMPILE AGDA2HS e #-}


-- And other exponents can be calculated by transforming a smallExp.
{-
exp : ∀ {a : Set} {{ara : AppRationals a}} {{pra : PrelengthSpace a}}
         -> (x : a) -> C a
exp x =
  if null <# x
    then recip (exp (negate x)) cheat
    else
     (if x <# (negate one)
        then {!let halfx = shiftl x (negsuc 0)!}
        else smallExp x cheat)
-}
