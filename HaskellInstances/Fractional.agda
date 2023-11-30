-- A Fractional instance of the reals,
-- using agda2hs' Haskell library.
-- Used to be able to integrate these reals
-- into Haskell programs.

{-# OPTIONS --erasure --guardedness #-}

module HaskellInstances.Fractional where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Fractional(..))
import RealTheory.Reals
import HaskellInstances.Num
#-}

open import Haskell.Prim.Fractional

import Algebra.Field
import Algebra.Ring
open import RealTheory.AppRationals
open import RealTheory.Completion
import RealTheory.Reals

open import HaskellInstances.Num

instance
  fractionalReal : {a : Set} {{ara : AppRationals a}} -> Fractional (C a)
  Fractional.super fractionalReal = numReal
  Fractional.RecipOK fractionalReal x = Algebra.Ring.NonZero x
  Fractional._/_ fractionalReal x y {{nonZeroy}} = x Algebra.Ring.* Algebra.Field.recip y nonZeroy
  Fractional.recip fractionalReal x {{nonZerox}} = Algebra.Field.recip x nonZerox
  {-# COMPILE AGDA2HS fractionalReal #-}
