-- Instances for Eq (mostly for QuickCheck tests).
{-# OPTIONS --erasure #-}
module HaskellInstance.Eq where

open import Agda.Builtin.Bool
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq

open import Algebra.SemiRing
open import Algebra.Ring
open import Implementation.Int
open import Implementation.Frac
open import Operator.Decidable
open import Shell.Exp hiding (Eq)

{-# FOREIGN AGDA2HS
import Prelude hiding ((*), negate)
#-}

instance
  -- We cannot use DecSetoid; it would result in Agda
  -- not knowing which instance to use.
  -- (Hm... what about the other way round? Defining DecSetoid with Eq?)
  eqFrac : ∀ {a : Set} {{semiRing : SemiRing a}} {{eq : Eq a}}
                      -> Eq (Frac a)
  Eq._==_ eqFrac x y = num x * den y == num y * den x
  {-# COMPILE AGDA2HS eqFrac #-}

  iEqExp : Eq Exp
  -- Ouch, so much boilerplate...
  (iEqExp Eq.== BoolLit x) (BoolLit y) = x == y
  (iEqExp Eq.== IntLit x) (IntLit y) = x == y
  (iEqExp Eq.== RatLit x) (RatLit y) = x == y
  (iEqExp Eq.== Var x) (Var y) = x == y
  (iEqExp Eq.== History x) (History y) = x == y
  (iEqExp Eq.== Neg x) (Neg y) = x == y
  (iEqExp Eq.== Not x) (Not y) = x == y
  (iEqExp Eq.== Pow x x') (Pow y y') = x == y && x' == y'
  (iEqExp Eq.== Div x x') (Div y y') = x == y && x' == y'
  (iEqExp Eq.== Mul x x') (Mul y y') = x == y && x' == y'
  (iEqExp Eq.== Sub x x') (Sub y y') = x == y && x' == y'
  (iEqExp Eq.== Add x x') (Add y y') = x == y && x' == y'
  (iEqExp Eq.== Lt x x') (Lt y y') = x == y && x' == y'
  (iEqExp Eq.== Le x x') (Le y y') = x == y && x' == y'
  (iEqExp Eq.== Exp.Eq x x') (Exp.Eq y y') = x == y && x' == y'
  (iEqExp Eq.== And x x') (And y y') = x == y && x' == y'
  (iEqExp Eq.== Or x x') (Or y y') = x == y && x' == y'
  (iEqExp Eq.== Pi) Pi = true
  (iEqExp Eq.== E) E = true
  (iEqExp Eq.== Expo x) (Expo y) = x == y
  (iEqExp Eq.== Sin x) (Sin y) = x == y
  (iEqExp Eq.== Cos x) (Cos y) = x == y
  (iEqExp Eq.== Sqrt x) (Sqrt y) = x == y
  -- Now some special cases.
  -- NOTE: this might be incomplete!
  (iEqExp Eq.== Neg (IntLit x)) (IntLit y) = x == negate y
  (iEqExp Eq.== IntLit x) (Neg (IntLit y)) = x == negate y
  (iEqExp Eq.== _) _ = false
  {-# COMPILE AGDA2HS iEqExp #-}
