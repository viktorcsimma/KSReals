-- Instances for converting simpler number types
-- to reals.
{-# OPTIONS --erasure #-}

module RealTheory.Instance.Cast where

open import Tool.Cheat

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int
open import Algebra.SemiRing
open import Algebra.Field
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Operator.Cast
open import RealTheory.MetricSpace
open import RealTheory.AppRational
open import RealTheory.Completion
open import RealTheory.Real

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer)
#-}

instance
  -- If you have an option, you'd better use addAQ or multByAQ or something like that.
  -- But when dividing by an integer, I don't have a better option yet
  -- than converting it to a real.
  castNatReal : ∀ {a : Set} {{ara : AppRational a}} -> Cast Nat (C a)
  Cast.cast castNatReal n = returnC (cast n)
  {-# COMPILE AGDA2HS castNatReal #-}
  castIntReal : ∀ {a : Set} {{ara : AppRational a}} -> Cast Int (C a)
  Cast.cast castIntReal n = returnC (cast n)
  {-# COMPILE AGDA2HS castIntReal #-}

  castRationalReal : ∀ {a : Set} {{ara : AppRational a}} -> Cast Rational (C a)
  Cast.cast castRationalReal (MkFrac n d dNotNull)
    = multByAQ (cast n) (recip (cast d) cheat)
  {-# COMPILE AGDA2HS castRationalReal #-}
