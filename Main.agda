-- A main program for demonstrating that
-- the implementation is indeed runnable.
{-# OPTIONS --erasure --guardedness #-}

{-# FOREIGN AGDA2HS
import Prelude (Integer, putStrLn)
import Implementations.Int (pos)

import RealTheory.Reals
import Tools.Show
#-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (Int; pos; negsuc)
import Agda.Builtin.IO
import Haskell.Prim.Show
import Haskell.Prim.String
import Haskell.Prim using (itsTrue)

open import Tools.Cheat

open import Tools.ErasureProduct
open import Algebra.Ring
open import Algebra.Field
open import Operations.Abs
open import Operations.Cast
open import Operations.Decidable
open import Operations.ShiftL
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Reals
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
open import Implementations.Dyadic
open import Implementations.DyadicReal
open import Functions.Exp
open import Tools.Show

postulate putStrLn : Haskell.Prim.String.String → Agda.Builtin.IO.IO ⊤

-- TODO: sin pi seems to only have a precision of 998 digits instead of 1000.

prec : Rational
prec = MkFrac (one) (shift one (pos 33219)) cheat -- that is log₂ (10^10000))
{-# COMPILE AGDA2HS prec #-}

toCalc : DReal
toCalc = exp (returnC (pos 1000 :|^ null))
{-# COMPILE AGDA2HS toCalc #-}

main : Agda.Builtin.IO.IO ⊤
main = putStrLn (Haskell.Prim.Show.show (fun toCalc (prec :&: Haskell.Prim.itsTrue)))
{-# COMPILE AGDA2HS main #-}
