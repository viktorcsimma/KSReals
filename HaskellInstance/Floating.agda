-- An instance of Floating for the reals.
-- Needed to use the test.hs program of Krebbers.
-- Written in Haskell since agda2hs doesn't have a Floating class yet
-- (and actually, I don't have all of the functions needed).
-- But it is still a .agda file so that I don't delete it accidentally
-- with other .hs files.
module HaskellInstance.Floating where

{-# FOREIGN AGDA2HS

import Algebra.Field
import Algebra.Ring
import qualified Functions.Exp
import qualified Functions.SquareRoot
import qualified Functions.Trigonometric
import RealTheory.AppRationals
import RealTheory.Completion
import HaskellInstances.Fractional

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
