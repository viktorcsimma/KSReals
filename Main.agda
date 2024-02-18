-- A main program for demonstrating that
-- the implementation is indeed runnable.
{-# OPTIONS --erasure --guardedness #-}

-- For being able to link with C++ code.
-- {-# FOREIGN AGDA2HS {-# LANGUAGE ForeignFunctionInterface #-} #-}

{-# FOREIGN AGDA2HS
import Prelude (Integer, putStrLn)
import Implementation.Int (pos)

import RealTheory.Reals
import Tool.Show
#-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (Int; pos; negsuc)
import Agda.Builtin.IO
import Haskell.Prim.Show
import Haskell.Prim.String
import Haskell.Prim using (itsTrue)

open import Tool.Cheat

open import Tool.ErasureProduct
open import Algebra.SemiRing
open import Algebra.Field
open import Operator.Abs
open import Operator.Cast
open import Operator.Decidable
open import Operator.Shift
open import RealTheory.AppRational
open import RealTheory.Completion
open import RealTheory.Reals
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Implementation.Dyadic
open import Implementation.DyadicReal
open import Function.Exp
open import Tool.Show

postulate putStrLn : Haskell.Prim.String.String → Agda.Builtin.IO.IO ⊤

-- TODO: sin pi seems to only have a precision of 998 digits instead of 1000.

prec : Rational
prec = MkFrac (one) (shift one (pos 33225)) cheat -- 33220 that is log₂ (10^10000))
{-# COMPILE AGDA2HS prec #-}

toCalc : DReal
toCalc = e
{-# COMPILE AGDA2HS toCalc #-}

{-
-- If we had a function called agdaMain which we want to call from C:
{-# FOREIGN AGDA2HS
foreign export ccall agdaMain :: Prelude.IO ()
 #-}
-}

main : Agda.Builtin.IO.IO ⊤
main = putStrLn (Haskell.Prim.Show.show
                (toDecimal (fun toCalc (prec :&: cheat))
                          10000))
{-# COMPILE AGDA2HS main #-}
