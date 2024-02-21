-- Infinite streams;
-- used later for construction of alternating power series
-- and the functions based on them.
{-# OPTIONS --erasure --guardedness #-}

module Tool.Stream where

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Haskell.Prim using (if_then_else_)

open import Tool.ErasureProduct

{-# FOREIGN AGDA2HS
import Prelude hiding (head, tail)
import qualified Prelude (head, tail)

import Tool.ErasureProduct
#-}

-- We have to give the fields a different name
-- so that we can use Prelude's head and tail
-- (maybe that gets optimised better).
record Stream {i}(a : Set i) : Set i where
  coinductive
  constructor mkStream
  field
    streamHead : a
    streamTail : Stream a

{-# FOREIGN AGDA2HS
-- Here, let's translate it to builtin lists
-- (I hope it is going to be more optimised this way).

type Stream a = [] a

mkStream :: a -> Stream a -> Stream a
mkStream = (:)
#-}

head : ∀{i}{a : Set i} -> Stream a -> a
head = Stream.streamHead
tail : ∀{i}{a : Set i} -> Stream a -> Stream a
tail = Stream.streamTail

{-# FOREIGN AGDA2HS
head :: Stream a -> a
head = Prelude.head
tail :: Stream a -> Stream a
tail = Prelude.tail
#-}

-- Generates a stream from a "seed",
-- a function giving an element from it
-- and a function returning the next seed.
coiteStream : ∀{i j}{a : Set i}{b : Set j}
                -> (a -> b) -> (a -> a) -> a -> Stream b
Stream.streamHead (coiteStream f g s) = f s
Stream.streamTail (coiteStream f g s) = coiteStream f g (g s)
{-# FOREIGN AGDA2HS
coiteStream :: (a -> b) -> (a -> a) -> a -> Stream b
coiteStream f g s = f s : coiteStream f g (g s)
#-}

-- Indexing.
index : ∀{i}{a : Set i} -> Stream a -> Nat -> a
index xs zero = head xs
index xs (suc n) = index (tail xs) n
{-# FOREIGN AGDA2HS
index :: Stream a -> Natural -> a
index xs n = xs !! (fromIntegral n)
#-}

-- Taking the first n elements
-- into a list.
takeStream : ∀{i}{a : Set i} -> Nat -> Stream a -> List a
takeStream zero xs = []
takeStream (suc n) xs = head xs ∷ takeStream n (tail xs)
{-# FOREIGN AGDA2HS
takeStream :: Natural -> Stream a -> [a]
takeStream n xs = take (fromIntegral n) xs
#-}

-- Counting elements
-- until there is one found
-- for which the predicate is false
-- (this might also depend on the index),
-- and returning the result along with the proof.
-- Needs a proof that there _is_ such an element.
-- (Maybe the proof's erased Nat could be used
-- for convincing the termination checker.)
{-# TERMINATING #-}
countWhile : ∀{i}{a : Set i}
                     -> (p : Nat -> a -> Bool)
                     -> (xs : Stream a)
                     -> @0 (Σ0 Nat (λ n -> p n (index xs n) ≡ false))
                     -> (Σ0 Nat (λ n -> p n (index xs n) ≡ false))
countWhile p xs hyp = go p xs hyp 0
  where
  -- This also contains an index.
  go : ∀{i}{a : Set i}
         -> (p : Nat -> a -> Bool)
         -> (xs : Stream a)
         -> @0 (Σ0 Nat (λ n -> p n (index xs n) ≡ false))
         -> Nat
         -> (Σ0 Nat (λ n -> p n (index xs n) ≡ false))
  go p xs hyp k = if (p k (head xs))
                  then proj₁ (go p (tail xs) cheat (1 + k)) :&: cheat
                  else k :&: cheat
{-# COMPILE AGDA2HS countWhile #-}

{-
-- Foldr'ing elements
-- until there is one found
-- for which the predicate is false.
-- Needs a proof that there _is_ such an element.
-- (foldr is lazy while foldl is not.)
{-# TERMINATING #-}
foldrWhile : ∀{i j}{a : Set i}{b : Set j}
                     -> (p : a -> Bool)
                     -> (a -> b -> b) -> b -> (xs : Stream a)
                     -> @0 (Σ0 Nat (λ n -> p (index xs n) ≡ false))
                     -> b
foldrWhile p f b xs hyp = if (p (head xs))
                                then f (head xs) (foldrWhile p f b (tail xs) cheat) 
                                else b
-}
