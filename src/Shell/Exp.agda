-- A data type for expressions.
{-# OPTIONS --erasure #-}
module Shell.Exp where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Haskell.Prim.String

open import Implementation.Decimal

{-# FOREIGN AGDA2HS
import Prelude hiding (Rational)
#-}

-- Because we have no real literals,
-- we don't actually need to know
-- the real type
data Exp : Set where
  BoolLit : Bool -> Exp
  NatLit : Nat -> Exp  -- negative integers will be get by negation
  DecimalLit : Decimal -> Exp
  -- Actually, real literals do not really exist;
  -- as you can only express irrational numbers
  -- with function outputs (maybe nullary, as with e and pi),
  -- which are parsable in themselves.

  Var : String -> Exp
  History : Nat -> Exp  -- contains the index; e.g. 1 is the last but one

  Neg Not : Exp -> Exp

  Pow Div Mul Sub Add Lt Le Eq And Or : Exp -> Exp -> Exp

  -- real functions
  Pi E : Exp
  Expo Sin Cos Sqrt : Exp -> Exp
{-# COMPILE AGDA2HS Exp #-}
