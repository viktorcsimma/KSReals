-- A definiton for uniform continuity.
module Continuity where

open import MetricSpace
open import Rational

record UniformlyContinuous {a b : Set} {{msa : MetricSpace a}} {{msb : MetricSpace b}}
                              (@0 f : a -> b) : Set where
  constructor WrapMod
  field
    modulus : PosRational -> PosRational
    @0 modulusCorrect : ∀ ε x y -> ball (modulus ε) x y
                                -> ball ε (f x) (f y)
open UniformlyContinuous public
{-# COMPILE AGDA2HS UniformlyContinuous #-}

-- What if we used instances for that?
                             
