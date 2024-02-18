-- A Number instance for the reals.
-- Actually, I don't use literals for reals as often;
-- I have written this rather as a requirement of Num.
{-# OPTIONS --erasure --guardedness #-}
module HaskellInstance.Number where

open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit

open import Algebra.Ring
open import Operator.Cast
open import RealTheory.AppRational
open import RealTheory.Completion
import RealTheory.Reals

instance
  numberReal : {a : Set} {{ara : AppRational a}} -> Number (C a)
  Number.Constraint numberReal _ = ⊤
  Number.fromNat numberReal n = returnC (cast n)
  {-# COMPILE AGDA2HS numberReal #-}
