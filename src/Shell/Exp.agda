-- A data type for expressions.
{-# OPTIONS --erasure #-}
module Shell.Exp where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Haskell.Prim.String

open import Implementation.Rational

{-# FOREIGN AGDA2HS
import Prelude hiding (Rational)
#-}

-- real is the real type used.
data Exp (real : Set) : Set where
  BoolLit : Bool -> Exp real
  IntLit : Int -> Exp real
  RatLit : Rational -> Exp real
  RealLit : real -> Exp real

  Var : String -> Exp real
  History : Nat -> Exp real  -- contains the index; e.g. 1 is the last but one

  Neg Not : Exp real -> Exp real

  Pow Div Mul Sub Add Lt Le Eq And Or : Exp real -> Exp real -> Exp real

  -- real functions
  Pi E : Exp real
  Expo Sin Cos Sqrt : Exp real -> Exp real
{-# COMPILE AGDA2HS Exp #-}
