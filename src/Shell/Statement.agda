-- Data type for statements
-- (assignments, control flow etc.)
{-# OPTIONS --erasure #-}

module Shell.Statement where

open import Agda.Builtin.List
open import Haskell.Prim.String

open import Shell.Exp

-- Represents a command given to the calculator.
-- We don't need to know the real type here either.
data Statement : Set where
  Empty : Statement -- the empty statement (empty string or only whitespace)
  Eval : Exp -> Statement -- when we simply want to evaluate an expression
  Assign : String -> Exp -> Statement
  If While : Exp -> List Statement -> Statement
{-# COMPILE AGDA2HS Statement #-}
