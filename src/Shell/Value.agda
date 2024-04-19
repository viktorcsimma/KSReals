-- A data type with possible result types of evaluating expressions
-- wrapped into it.
{-# OPTIONS --erasure #-}

module Shell.Value where

open import Agda.Builtin.Bool
open import Agda.Builtin.Int

open import Implementation.Rational

open import Shell.Exp

{-# FOREIGN AGDA2HS
import Prelude hiding (Rational)
#-}

-- Represents a result of a computation,
-- with four possible types.
-- real is the real type used.
data Value (real : Set) : Set where
  VBool : Bool -> Value real
  VInt : Int -> Value real
  VRat : Rational -> Value real
  VReal : real -> Value real
{-# COMPILE AGDA2HS Value #-}

