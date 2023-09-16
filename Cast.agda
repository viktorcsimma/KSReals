-- A type class for pair of types
-- for which there is a "canonical" cast operation.
module Cast where

open import Haskell.Prim using (id)

record Cast (a b : Set) : Set₁ where
  field
    cast : a -> b
open Cast {{...}} public
{-# COMPILE AGDA2HS Cast class #-}

instance
  castSame : ∀ {a : Set} -> Cast a a
  Cast.cast castSame = id
  {-# COMPILE AGDA2HS castSame #-}
