-- Data type for statements
-- (assignments, control flow etc.)
{-# OPTIONS --erasure #-}

module Shell.Statement where

open import Agda.Builtin.List
open import Haskell.Prim.String

open import Shell.Exp

-- real is the real type used.
data Statement (real : Set) : Set where
  Empty : Statement real -- the empty statement (empty string or only whitespace)
  Eval : Exp real -> Statement real -- when we simply want to evaluate an expression
  Assign : String -> Exp real -> Statement real
  If While : Exp real -> List (Statement real) -> Statement real
{-# COMPILE AGDA2HS Statement #-}
