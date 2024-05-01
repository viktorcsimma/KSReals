-- An instance of Floating for the reals.
-- Needed to use the test.hs program of Krebbers.
-- Written in Haskell since agda2hs doesn't have a Floating class yet
-- (and actually, I don't have all of the functions needed).
-- But it is still a .agda file so that I don't delete it accidentally
-- with other .hs files.
{-# OPTIONS --erasure --guardedness #-}
module HaskellInstance.Floating where

-- For agda2hs to know dependencies.
import Algebra.Field
import Algebra.Ring
import Function.Exp
import Function.SquareRoot
import Function.Trigonometric
import RealTheory.AppRational
import RealTheory.Completion
import HaskellInstance.Fractional

{-# FOREIGN AGDA2HS

import Algebra.Field
import Algebra.Ring
import qualified Function.Exp
import qualified Function.SquareRoot
import qualified Function.Trigonometric
import RealTheory.AppRational
import RealTheory.Completion
import HaskellInstance.Fractional

-- For error messages.
notImplemented :: String -> String
notImplemented = (++ " has not been implemented yet")

instance (AppRationals a) => Floating (C a) where
  pi = Functions.Trigonometric.pi
  exp = Functions.Exp.exp
  log = error $ notImplemented "log"
  sqrt = Functions.SquareRoot.sqrt
  logBase = error $ notImplemented "logBase"
  sin = Functions.Trigonometric.sin
  cos = error $ notImplemented "cos"
  tan = error $ notImplemented "tan"
  asin = error $ notImplemented "asin"
  acos = error $ notImplemented "cos"
  atan = error $ notImplemented "atan"
  sinh = error $ notImplemented "sinh"
  cosh = error $ notImplemented "cosh"
  tanh = error $ notImplemented "tanh"
  asinh = error $ notImplemented "asinh"
  acosh = error $ notImplemented "acosh"
  atanh = error $ notImplemented "atanh"
#-}
