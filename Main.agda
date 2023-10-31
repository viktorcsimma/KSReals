-- A main program for demonstrating that
-- the implementation is indeed runnable.
{-# OPTIONS --erasure #-}

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (IO, Show, putStrLn, show)

import Implementations.Int
import RealTheory.Reals
import Tools.Show
#-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (pos; negsuc)
open import Agda.Builtin.IO
open import Haskell.Prim.Show
open import Haskell.Prim.String
open import Haskell.Prim

open import Tools.Cheat

open import Tools.ErasureProduct
open import Algebra.Ring
open import Algebra.Field
open import Operations.ShiftL
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Reals
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
open import Implementations.Dyadic
open import Implementations.DyadicReal
open import Function.Exp
open import Tools.Show

postulate putStrLn : String → IO ⊤

toCalc : DReal
toCalc = recip (smallExpQ (negate one :&: cheat)) cheat
{-# COMPILE AGDA2HS toCalc #-}

main : IO ⊤
main = putStrLn (show (fun toCalc
                        (MkFrac (pos 1)
                        (shift (pos 1) (hsFromIntegral (pos 33219)))  -- that is log₂ (10^10000)
                           tt :&: itsTrue)))
{-# COMPILE AGDA2HS main #-}
