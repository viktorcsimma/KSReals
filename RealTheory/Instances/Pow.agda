-- An integer power function for reals;
-- based on O'Connor's intPowerCts.
{-# OPTIONS --erasure #-}

module RealTheory.Instances.Pow where

open import Tools.Cheat

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim using (id; itsTrue)

open import Algebra.Field
open import Algebra.MetricSpace
open import Algebra.Order
open import Algebra.Ring
open import Implementations.Nat
open import Implementations.Int
open import Implementations.Rational
open import Operations.Abs
open import Operations.Cast
open import Operations.Decidable
open import Operations.Pow
open import RealTheory.AppRationals
open import RealTheory.Completion
open import RealTheory.Continuity
open import RealTheory.Interval
open import RealTheory.Reals
open import Tools.ErasureProduct

{-# FOREIGN AGDA2HS
import qualified Prelude

import Algebra.Field
import Algebra.Ring
import Implementations.Nat
import Operations.Cast
import Operations.Pow
import RealTheory.Continuity
import Tools.ErasureProduct
#-}

ucNatPower : ∀ {a : Set} {{ara : AppRationals a}}
               -> (c : a) -- an upper bound; x can only be in [-c,c] to preserve uniform continuity
               -> (n : Nat) -- the exponent
               -> UcFun (Σ0 a (IsIn [ negate c , c ])) a
ucNatPower c zero = proj₁ :^: WrapMod id cheat
ucNatPower c n@(suc nm1) = (λ Σx -> proj₁ Σx ^ n)               -- v this is the derivative in c
                              :^: WrapMod (λ ε -> proj₁ ε * recip (cast n * cast (c ^ nm1)) cheat :&: cheat )
                                          cheat
{-# FOREIGN AGDA2HS
ucNatPower :: AppRationals a => a -> Nat -> UcFun (Σ0 a) a
ucNatPower _ 0 = prefixCon proj₁ (WrapMod Prelude.id)
ucNatPower c n = prefixCon (\ sx -> proj₁ sx ^ n) (WrapMod (\ ε -> (:&:) (proj₁ ε * recip (cast n * cast (c ^ (n Prelude.- 1))))))
#-}

instance
  powRealNat : ∀ {a : Set} {{ara : AppRationals a}}
               -> Pow (C a) Nat
  Pow._^_ (powRealNat {a}) x n = let cx = compress x; bound = canonicalBound x
                           in mapC {{prelengthInterval {a} {[ negate bound , bound ]}}}
                               (ucNatPower bound n)
                               (MkC (λ ε -> fun cx ε :&: cheat)  -- we simply put it into the Σ0 format
                                cheat)
  Pow.powProper powRealNat = cheat
  Pow.powNull powRealNat = cheat
  Pow.powSuc powRealNat = cheat
  {-# COMPILE AGDA2HS powRealNat #-}

-- For integer exponents, we would have to specify
-- that x must not be zero.
