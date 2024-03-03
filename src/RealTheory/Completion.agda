-- The definition of the completion monad.
-- This makes a prelength space Cauchy complete.
{-# OPTIONS --erasure #-}

module RealTheory.Completion where

{-# FOREIGN AGDA2HS
import qualified Prelude
import Prelude (Integer, const, (.))

import Implementation.Int
import Implementation.Rational
import Algebra.SemiRing
import Algebra.Ring
#-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Haskell.Prim.Tuple
open import Haskell.Prim using (_∘_; const; id)

open import Tool.Cheat

open import Tool.ErasureProduct
open import RealTheory.MetricSpace
open import Algebra.Setoid
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Order
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import Operator.Cast
open import RealTheory.Continuity
open import RealTheory.Interval

-- The problem is that we cannot include the condition in the type.
-- That's because the Functor, Monad etc. instances all expect a Set -> Set,
-- without class instances.


-- And even if we could do that;
-- only continuous functions can be given to `bind`,
-- as it uses the modulus of continuity for calculation.

-- So we'll simply write the return and bind operations for C
-- and create simple shortenings for them.

-- This will be a newtype in Haskell.
-- Sometimes, the range of a function might not be a prelength space;
-- hence we allow this.
record C (a : Set) {{metricSpace : MetricSpace a}}
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

-- For ease of use,
-- we define cast operators
-- with the help of returnC.
{-
This conflicts with castNatAQ for some reason.
instance
  castC : ∀ {a b : Set} {{prelengthSpace : PrelengthSpace b}}
                -> {{Cast a b}} -> Cast a (C b)
  Cast.cast castC x = returnC (cast x)
  {-# COMPILE AGDA2HS castC #-}
-}

instance
  setoidC : ∀ {a : Set} {{psa : MetricSpace a}} -> Setoid (C a)
  Setoid._≃_ setoidC x y = ∀ (ε : PosRational) ->
                                   ball (plusPos ε ε) (fun x ε) (fun y ε)
  Setoid.≃-refl (setoidC {a}) {x = x} ε = ballReflexive (plusPos ε ε) (fun x ε) (fun x ε) (≃-refl {a})
  Setoid.≃-sym setoidC = cheat
  Setoid.≃-trans setoidC = cheat
  {-# COMPILE AGDA2HS setoidC #-}

  metricC : ∀ {a : Set} {{psa : MetricSpace a}} -> MetricSpace (C a)
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

  setoidΣ0 : ∀ {a : Set} {{setoid : Setoid a}}
               {@0 Subset : a -> Set}
               -> Setoid (Σ0 a Subset)
  Setoid._≃_ setoidΣ0 (x :&: _) (y :&: _) = x ≃ y
  Setoid.≃-refl setoidΣ0 = cheat
  Setoid.≃-sym setoidΣ0 = cheat
  Setoid.≃-trans setoidΣ0 = cheat
  {-# COMPILE AGDA2HS setoidΣ0 #-}

  metricΣ0 : ∀ {a : Set} {{metric : MetricSpace a}}
               {@0 Subset : a -> Set}
               -> MetricSpace (Σ0 a Subset)
  MetricSpace.setoid metricΣ0 = setoidΣ0
  MetricSpace.ball metricΣ0 ε (x :&: _) (y :&: _) = ball ε x y
  MetricSpace.ballReflexive metricΣ0 = cheat
  MetricSpace.ballSym metricΣ0 = cheat
  MetricSpace.ballTriangle metricΣ0 = cheat
  MetricSpace.ballClosed metricΣ0 = cheat
  MetricSpace.ballEq metricΣ0 = cheat
  {-# COMPILE AGDA2HS metricΣ0 #-}

  -- Are we sure that this is true?
  -- Maybe we should have a stronger constraint on the original prelength space
  -- to make sure that Σ0 a _ is a prelength space.
  prelengthΣ0 : ∀ {a : Set} {{metric : PrelengthSpace a}}
                  {@0 Subset : a -> Set}
                  -> PrelengthSpace (Σ0 a Subset)
  PrelengthSpace.metricSpace prelengthΣ0 = metricΣ0
  PrelengthSpace.prelength (prelengthΣ0 {a})
                              ε δ₁ δ₂
                              (x :&: hypx) (y :&: hypy)
                              ε<δ₁+δ₂
                              bεxy
                           = (proj₁ oldPack :&: cheat) :&: proj₂ oldPack
    where
    oldPack : Σ0 a
      (λ z → ball δ₁ x z × ball δ₂ z y)
    oldPack = prelength ε δ₁ δ₂ x y ε<δ₁+δ₂ bεxy
  -- {-# COMPILE AGDA2HS prelengthΣ0 #-} -- GHC sees this as a duplicate of the next instance

  -- the instance must not have the same name as the function!
  prelengthInterval : ∀ {a : Set} {{prelengtha : PrelengthSpace a}} {{le : Le a}} {{lt : Lt a}}
               {@0 I : Interval a}
               -> PrelengthSpace (Σ0 a (IsIn I))
  PrelengthSpace.metricSpace prelengthInterval = metricΣ0
  PrelengthSpace.prelength (prelengthInterval {a}) ε δ₁ δ₂ (x :&: _) (y :&: _)
                                         ε<δ₁+δ₂
                                         bεxy
                                         -- hm... is this actually true?
                                         -- maybe it's only true for intervals
                                         -- and only if the metric is the ∣x-y∣≤ε metric
                                         -- TODO
                                         = (proj₁ prelengthPack :&: cheat) :&: proj₂ prelengthPack
    where
    prelengthPack : Σ0 a (λ z -> ball δ₁ x z × ball δ₂ z y)
    prelengthPack = prelength ε δ₁ δ₂ x y ε<δ₁+δ₂ bεxy
  {-# COMPILE AGDA2HS prelengthInterval #-}

join : ∀ {a : Set} {{metric : MetricSpace a}} -> C (C a) -> C a
join x = MkC (λ ε -> fun (fun x (halvePos ε)) (halvePos ε)) cheat
{-# COMPILE AGDA2HS join #-}

ucJoin : ∀ {a : Set} {{metric : MetricSpace a}} -> UniformlyContinuous (join {a})
ucJoin = WrapMod id cheat
{-# FOREIGN AGDA2HS
ucJoin :: UniformlyContinuous
ucJoin = WrapMod Prelude.id
#-}

-- map f x is regular when a is a prelength space.
-- So the range might be a simple metric space.
mapC : {a b : Set} {{pra : PrelengthSpace a}} {{metricb : MetricSpace b}}
         -> UcFun a b -> (C a -> C b)
mapC (f :^: WrapMod μ hyp) x = MkC (f ∘ fun x ∘ μ) cheat
{-# COMPILE AGDA2HS mapC #-}

ucMapC : {a b : Set} {{pra : PrelengthSpace a}} {{prb : PrelengthSpace b}}
         -> (f : a -> b) (ucf : UniformlyContinuous f) (x : C a)
         -> UniformlyContinuous (mapC (f :^: ucf))
ucMapC f (WrapMod μ hyp) x = WrapMod μ cheat
{-# COMPILE AGDA2HS ucMapC #-}

bindC : ∀ {a b : Set} {{psa : PrelengthSpace a}} {{psb : PrelengthSpace b}}
          -> UcFun a (C b)
          -> UcFun (C a) (C b)
bindC f = join ∘ mapC f :^: WrapMod (modulus (proj₂' f)) cheat {-(λ ca -> MkC (λ ε -> fun (f ((fun ca) (μ (halvePos ε)))) (halvePos ε))
                                 {!!}) :^: {!!}-}
{-# COMPILE AGDA2HS bindC #-}

-- A more convenient operator for this.
infixl 1 _#>>=_
_#>>=_ : ∀ {a b : Set} {{psa : PrelengthSpace a}} {{psb : PrelengthSpace b}}
             {@0 Subset : a -> Set}
          -> C a -> (f : a -> C b) -> UniformlyContinuous f -> C b
(csa #>>= f) ucf = proj₁' (bindC (f :^: ucf)) csa
{-# COMPILE AGDA2HS _#>>=_ #-} 

-- The function space with the supremum norm.
instance
  setoidFun : {a b : Set} {{pra : Setoid a}} {{prb : Setoid b}}
         -> Setoid (a -> b)
  Setoid._≃_ setoidFun f g = ∀ x -> f x ≃ g x
  Setoid.≃-refl setoidFun = cheat
  Setoid.≃-sym setoidFun = cheat
  Setoid.≃-trans setoidFun = cheat
  {-# COMPILE AGDA2HS setoidFun #-}

  setoidUcFun : {a b : Set} {{pra : MetricSpace a}} {{prb : MetricSpace b}}
         -> Setoid (UcFun a b)
  Setoid._≃_ setoidUcFun = λ (f :^: _) (g :^: _) -> f ≃ g
  Setoid.≃-refl setoidUcFun {x = f :^: _} = ≃-refl {x = f}
  Setoid.≃-sym setoidUcFun {x = f :^: _} {y = g :^: _} eq = ≃-sym {x = f} {y = g} eq
  Setoid.≃-trans setoidUcFun {x = f :^: _} {y = g :^: _} {z = h :^: _} eq1 eq2
                                             = ≃-trans {x = f} {y = g} {z = h} eq1 eq2
  {-# COMPILE AGDA2HS setoidUcFun #-}

  metricUcFun : {a b : Set} {{pra : MetricSpace a}} {{prb : MetricSpace b}}
         -> MetricSpace (UcFun a b)
  MetricSpace.setoid metricUcFun = setoidUcFun
  MetricSpace.ball (metricUcFun {a = a})
       ε (f :^: _) (g :^: _) = ∀ (x : a) -> ball ε (f x) (g x)
  MetricSpace.ballReflexive metricUcFun = cheat
  MetricSpace.ballSym metricUcFun = cheat
  MetricSpace.ballTriangle metricUcFun = cheat
  MetricSpace.ballClosed metricUcFun = cheat
  MetricSpace.ballEq metricUcFun = cheat
  {-# COMPILE AGDA2HS metricUcFun #-}

ap : {a b : Set} {{pra : PrelengthSpace a}} {{prb : PrelengthSpace b}}
         -> C (UcFun a b) -> C a -> C b
ap (MkC f _) x = MkC (λ ε -> fun (mapC (f (halvePos ε)) x) (halvePos ε)) cheat
{-# COMPILE AGDA2HS ap #-}

map2 : {a b c : Set} {{pra : PrelengthSpace a}} {{prb : PrelengthSpace b}} {{prc : PrelengthSpace c}}
         -> UcFun a (UcFun b c) -> (C a -> C b -> C c)
map2 f = ap ∘ mapC f
{-# COMPILE AGDA2HS map2 #-}
