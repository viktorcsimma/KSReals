-- The definition of the completion monad.
-- This makes a prelength space Cauchy complete.
module Complete where

open import Agda.Builtin.Unit
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Functor
open import Haskell.Prim.Applicative
open import Haskell.Prim.Monad
open Do -- we want agda2hs to use do-notation
open import Haskell.Prim.Tuple
open import Haskell.Prim using (_∘_; const)

open import Cheat

open import ErasureProduct
open import Setoid
open import Ring
open import Order
open import Int
open import Rational
open import MetricSpace
open import Continuity
open import Operations

-- The problem is that we cannot include the condition in the type.
-- That's because the Functor, Monad etc. instances all expect a Set -> Set,
-- without class instances.


-- And even if we could do that;
-- only continuous functions can be given to `bind`,
-- as it uses the modulus of continuity for calculation.

-- So we'll simply write the return and bind operations for C
-- and create simple shortenings for them.

-- This will be a newtype in Haskell.
record C (a : Set) {{prelengthSpace : PrelengthSpace a}}
              : Set where
  constructor MkC
  field
    fun : PosRational -> a
    @0 reg : ∀ (ε₁ ε₂ : PosRational)
               -> ball (plusPos ε₁ ε₂) (fun ε₁) (fun ε₂)
open C public
{-# COMPILE AGDA2HS C newtype #-}

returnC : ∀ {a : Set} {{prelengthSpace : PrelengthSpace a}}
            -> a -> C a
returnC {a} x = MkC (const x)
                    λ ε₁ ε₂ -> ballReflexive (plusPos ε₁ ε₂) x x (≃-refl {a})
{-# COMPILE AGDA2HS returnC #-}

instance
  setoidC : ∀ {a : Set} {{psa : PrelengthSpace a}} -> Setoid (C a)
  Setoid._≃_ setoidC x y = ∀ (ε : PosRational) ->
                                   ball (plusPos ε ε) (fun x ε) (fun y ε)
  Setoid.≃-refl (setoidC {a}) {x = x} ε = ballReflexive (plusPos ε ε) (fun x ε) (fun x ε) (≃-refl {a})
  Setoid.≃-sym setoidC = cheat
  Setoid.≃-trans setoidC = cheat
  {-# COMPILE AGDA2HS setoidC #-}

  metricC : ∀ {a : Set} {{psa : PrelengthSpace a}} -> MetricSpace (C a)
  MetricSpace.setoid metricC = setoidC
  MetricSpace.ball metricC ε x y = ∀ (δ₁ δ₂ : PosRational)
                                     -> ball (plusPos (plusPos ε δ₁) δ₂)
                                             (fun x δ₁)
                                             (fun x δ₂)
  MetricSpace.ballReflexive metricC = cheat
  MetricSpace.ballSym metricC = cheat
  MetricSpace.ballTriangle metricC = cheat
  MetricSpace.ballClosed metricC = cheat
  MetricSpace.ballEq metricC = cheat
  {-# COMPILE AGDA2HS metricC #-}

  prelengthC : ∀ {a : Set} {{psa : PrelengthSpace a}} -> PrelengthSpace (C a)
  PrelengthSpace.metricSpace prelengthC = metricC
  PrelengthSpace.prelength (prelengthC {a}) ε δ₁ δ₂ x y ε<δ₁+δ₂ ballεxy
        = returnC (proj₁ cPack) :&: cheat
    where
     γ δ₁mγ δ₂mγ : PosRational
     γ = (proj₁ δ₁ + proj₁ δ₂ + negate (proj₁ ε)) * MkFrac (pos 1) (pos 5) tt
            :&: cheat
     δ₁mγ = proj₁ δ₁ + negate (proj₁ γ) :&: cheat
     δ₂mγ = proj₁ δ₂ + negate (proj₁ γ) :&: cheat
     cPack : Σ0 a (λ c -> (ball δ₁mγ (fun x γ) c) × (ball δ₂mγ c (fun y γ)))
     cPack = prelength {a} (plusPos ε (plusPos γ γ)) δ₁mγ δ₂mγ (fun x γ) (fun y γ) cheat cheat
  {-# COMPILE AGDA2HS prelengthC #-}

bindC : ∀ {a b : Set} {{psa : PrelengthSpace a}} {{psb : PrelengthSpace b}}
          -> (f : a -> C b) -> UniformlyContinuous f
          -> C a -> C b
bindC f (WrapMod μ hyp) ca = MkC (λ ε -> fun (f (fun ca (μ (halvePos ε)))) (halvePos ε))
                                 cheat
{-# COMPILE AGDA2HS bindC #-}

-- A more convenient operator for this.
infixl 1 _#>>=_
_#>>=_ : ∀ {a b : Set} {{psa : PrelengthSpace a}} {{psb : PrelengthSpace b}}
          -> C a -> (f : a -> C b) -> UniformlyContinuous f -> C b
(ca #>>= f) ucf = bindC f ucf ca
{-# COMPILE AGDA2HS _#>>=_ #-}

map : {a b : Set} {{pra : PrelengthSpace a}} {{prb : PrelengthSpace b}}
         -> (f : a -> b) -> UniformlyContinuous f -> (C a -> C b)
map f (WrapMod μ hyp) x = MkC (f ∘ fun x ∘ μ) cheat
{-# COMPILE AGDA2HS map #-}

ucMap : {a b : Set} {{pra : PrelengthSpace a}} {{prb : PrelengthSpace b}}
         -> (f : a -> b) (ucf : UniformlyContinuous f) (x : C a)
         -> UniformlyContinuous (map f ucf)
ucMap f (WrapMod μ hyp) x = WrapMod μ cheat
{-# COMPILE AGDA2HS ucMap #-}


-- The function space with the supremum norm.
instance
  setoidFun : {a b : Set} {{pra : Setoid a}} {{prb : Setoid b}}
         -> Setoid (a -> b)
  Setoid._≃_ setoidFun f g = ∀ x -> f x ≃ g x
  Setoid.≃-refl setoidFun = cheat
  Setoid.≃-sym setoidFun = cheat
  Setoid.≃-trans setoidFun = cheat
  {-# COMPILE AGDA2HS setoidFun #-}

  metricFun : {a b : Set} {{pra : MetricSpace a}} {{prb : MetricSpace b}}
         -> MetricSpace (Σ' (a -> b) UniformlyContinuous)
  Setoid._≃_ (MetricSpace.setoid metricFun) = λ (f :^: _) (g :^: _) -> f ≃ g
  Setoid.≃-refl (MetricSpace.setoid metricFun) = {!!}
  Setoid.≃-sym (MetricSpace.setoid metricFun) = {!!}
  Setoid.≃-trans (MetricSpace.setoid metricFun) = {!!}
  MetricSpace.ball metricFun ε (f :^: _) (g :^: _) = ∀ x -> ball ε (f x) (g x)
  MetricSpace.ballReflexive metricFun = {!!}
  MetricSpace.ballSym metricFun = {!!}
  MetricSpace.ballTriangle metricFun = {!!}
  MetricSpace.ballClosed metricFun = {!!}
  MetricSpace.ballEq metricFun = {!!}
  {-# COMPILE AGDA2HS metricFun #-}

{-

ap

map2 : {a b c : Set} {{pra : PrelengthSpace a}} {{prb : PrelengthSpace b}} {{prc : PrelengthSpace c}}
         -> (f : a -> Σ' (b -> c) UniformlyContinuous) -> UniformlyContinuous f -> (C a -> C b -> C c)
map2 f ucf = {!!}
{-# COMPILE AGDA2HS map2 #-}
-}
