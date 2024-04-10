-- Contains definitions related to
-- creating a non-erased existence proof from an erased one
-- by trying out possibilities brute-force.
{-# OPTIONS --erasure #-}
module Tool.Witness where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Haskell.Prim.Tuple using (_↔_; _,_; fst)
open import Haskell.Prim using (IsTrue; itsTrue)

open import Tool.PropositionalEquality
open import Tool.ErasureProduct

{-# FOREIGN AGDA2HS
import qualified Prelude
import Numeric.Natural
import Tool.ErasureProduct
#-}

-- The equivalence of _≡ true and IsTrue.
-- Maybe this is still the most logical place for it;
-- it has quite a lot of dependencies to be put to a lower-level module.
@0 ≡true↔IsTrue : ∀ (x : Bool) → x ≡ true ↔ IsTrue x
≡true↔IsTrue false = (λ {()}) , (λ {()})
≡true↔IsTrue true = (λ _ -> itsTrue) , λ _ -> refl

-- Creating a non-erased natural existence proof from an erased one
-- (essentially, calculating a witness)
-- if the property is decidable.
-- This is needed for the inverse.
-- I don't yet know how we could prove the termination of this.
{-# TERMINATING #-}
witness : ∀ (p : Nat -> Bool) (@0 erasedProof : Σ0 Nat (λ n -> IsTrue (p n)))
                -> Σ0 Nat (λ n -> IsTrue (p n))
witness p (n :&: hyp) = go 1 n
  where
  -- Could we use this to prove termination somehow?
  @0 pred : Nat -> Nat
  pred zero = zero
  pred (suc n) = n
  
  go : Nat -> @0 Nat -> Σ0 Nat (λ n -> IsTrue (p n))
  go n n0 with p n in hyp
  ... | true = n :&: fst (≡true↔IsTrue (p n)) hyp
  ... | false = go (suc n) (pred n0)
-- Tried it with if-then-else, but then it got stuck at the next one.
{-# FOREIGN AGDA2HS
-- Since posRCrit already uses shifting,
-- we go here incrementally, too.
-- This way, it remains correct
-- even if there is only a finite amount of good witnesses.
witness :: (Natural -> Prelude.Bool) -> Σ0 Natural
witness p = (:&:) (Prelude.until p (1 Prelude.+) 1)
#-}
