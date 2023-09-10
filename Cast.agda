-- A type class for pair of types
-- for which there is a "canonical" cast operation.
module Cast where

record Cast (a b : Set) : Set₁ where
  field
    cast : a -> b
open Cast {{...}} public
{-# COMPILE AGDA2HS Cast class #-}
