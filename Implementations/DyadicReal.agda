-- A concrete implementation of the reals
-- based on dyadic rationals.
{-# OPTIONS --erasure #-}

module Implementations.DyadicReal where

open import RealTheory.AppRationals
open import Implementations.Dyadic
open import RealTheory.Completion

DReal : Set
DReal = C Dyadic
{-# COMPILE AGDA2HS DReal #-}
