-- A Num instance of the reals,
-- using agda2hs' Haskell library.
-- Used to be able to integrate these reals
-- into Haskell programs.
{-# OPTIONS --erasure --guardedness #-}

module HaskellInstance.Num where

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Agda.Builtin.FromNat
open import Agda.Builtin.Unit
open import Haskell.Prim.Num
open Haskell.Prim.Num using (Num)

import Algebra.Field
import Algebra.SemiRing
import Algebra.Ring
import Implementation.Int
import Operator.Abs
open import Operator.Cast
open import RealTheory.AppRational
open import RealTheory.Completion
import RealTheory.Real

open import HaskellInstance.Number

{-# FOREIGN AGDA2HS
import RealTheory.Real
#-}

instance
  numReal : {a : Set} {{ara : AppRational a}} -> Num (C a)
  Num.MinusOK numReal _ _ = ⊤
  Num.NegateOK numReal _ = ⊤
  Num.FromIntegerOK numReal _ = ⊤
  Num._+_ numReal x y = x Algebra.SemiRing.+ y
  Num._-_ numReal x y = x Algebra.Ring.- y
  Num._*_ numReal x y = x Algebra.SemiRing.* y
  Num.negate numReal x = Algebra.Ring.negate x
  Num.abs numReal x = Operator.Abs.abs x
  Num.signum (numReal {a}) _ = returnC (cast 42)    -- well... we cannot do anything here
  Num.fromInteger numReal x = returnC (cast x)
  Num.number numReal = HaskellInstance.Number.numberReal
  Num.numZero (numReal {a}) = tt
  Num.numOne (numReal {a}) = tt
  {-# COMPILE AGDA2HS numReal #-}
