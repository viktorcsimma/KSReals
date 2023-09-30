-- A definiton for uniform continuity.
module RealTheory.Continuity where

open import Agda.Builtin.Unit

open import Algebra.Order
open import Algebra.MetricSpace
open import Implementations.Rational
open import Tools.ErasureProduct

{-
-- Actually, we don't need subsets here.
-- If we want to use subsets, we'll use Σ0 a P instead of a.

-- As not all metric spaces are ordered, we use a more general subset concept.
record UniformlyContinuousOn {a b : Set} {{msa : MetricSpace a}} {{msb : MetricSpace b}}
                              (@0 Subset : a -> Set) (@0 f : a -> b) : Set where
  constructor WrapMod
  field
    modulus : PosRational -> PosRational
    @0 modulusCorrect : ∀ ε x y -> Subset x -> Subset y
                                -> ball (modulus ε) x y
                                -> ball ε (f x) (f y)
open UniformlyContinuousOn public
{-# COMPILE AGDA2HS UniformlyContinuousOn newtype #-}

UcFunOn : {a : Set} {{msa : MetricSpace a}}
          (@0 Subset : a -> Set)
          (b : Set) {{msb : MetricSpace b}}
             -> Set
UcFunOn {a} subset b = Σ' (a -> b) (UniformlyContinuousOn subset)
{-# COMPILE AGDA2HS UcFunOn #-}
-}


record UniformlyContinuous {a b : Set} {{msa : MetricSpace a}} {{msb : MetricSpace b}}
                              (@0 f : a -> b) : Set where
  constructor WrapMod
  field
    modulus : PosRational -> PosRational
    @0 modulusCorrect : ∀ ε x y -> ball (modulus ε) x y
                                -> ball ε (f x) (f y)
open UniformlyContinuous public
{-# COMPILE AGDA2HS UniformlyContinuous newtype #-}

-- What if we used instances for that?

UcFun : (a b : Set) {{msa : MetricSpace a}} {{msb : MetricSpace b}}
             -> Set
UcFun a b = Σ' (a -> b) UniformlyContinuous
{-# COMPILE AGDA2HS UcFun #-}
