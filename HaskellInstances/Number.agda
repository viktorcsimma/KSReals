-- A Number instance for the reals.
-- Actually, I don't use literals for reals as often;
-- I have written this rather as a requirement of Num.
{-# OPTIONS --erasure --guardedness #-}
module HaskellInstances.Number where

open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit

open import Algebra.Ring
open import Operations.Cast
open import RealTheory.AppRationals
open import RealTheory.Completion
import RealTheory.Reals

instance
  numberReal : {a : Set} {{ara : AppRationals a}} -> Number (C a)
  Number.Constraint numberReal _ = ⊤
  Number.fromNat numberReal n = returnC (cast n)
  {-# COMPILE AGDA2HS numberReal #-}
