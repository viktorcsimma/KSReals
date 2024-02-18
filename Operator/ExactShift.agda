-- And now a separate class for when
-- shifting to the right is exact and does not come with loss of precision
-- (used for the rationals and dyadics).
-- A type class for types
-- which have a shift operation
-- (that is, shifting with an integer
-- which might also be negative).
{-# OPTIONS --erasure #-}

module Operator.ExactShift where

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_+_; _*_)
open import Agda.Builtin.Int
open import Haskell.Prim.Tuple

open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Operator.Pow
open import Implementation.Nat
open import Implementation.Int

open import Operator.Shift

{-# FOREIGN AGDA2HS
-- for the builtin shift:
import qualified Data.Bits (shift)

import Implementation.Nat
import Implementation.Int
import Algebra.SemiRing hiding ((*))
#-}

record ExactShift (a : Set) : Set₁ where
  field
    overlap {{super}} : Shift a
    @0 shiftRightThenLeft : ∀ (x : a) (n : Nat) -> shift (shift x (negate (pos n))) (pos n) ≃ x
open ExactShift {{...}} public
{-# COMPILE AGDA2HS ExactShift class #-}
