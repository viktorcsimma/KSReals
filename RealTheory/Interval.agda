-- A definition of closed intervals on ordered sets
-- and a way to convert them to predicates.
{-# OPTIONS --erasure #-}

module RealTheory.Interval where

open import Agda.Builtin.Unit
open import Haskell.Prim.Tuple

open import Algebra.Order

data Interval (a : Set) {{le : Le a}} : Set where
  [_,_] [_,_[ ]_,_] ]_,_[ : a -> a -> Interval a
  [_,+∞[ : a -> Interval a
  ]-∞,_] : a -> Interval a
  ]-∞,+∞[ : Interval a

@0 IsIn : {a : Set} {{le : Le a}} {{lt : Lt a}} -> Interval a -> a -> Set
IsIn [ a , b ] x = a ≤ x × x ≤ b
IsIn [ a , b [ x = a ≤ x × x < b
IsIn ] a , b ] x = a < x × x ≤ b
IsIn ] a , b [ x = a < x × x < b
IsIn [ a ,+∞[  x  = a ≤ x
IsIn ]-∞, b ]  x  = x ≤ b
IsIn ]-∞,+∞[   _   = ⊤
