-- A concrete implementation of the reals
-- based on dyadic rationals.
{-# OPTIONS --erasure #-}

module Implementation.DyadicReal where

open import RealTheory.AppRational
open import Implementation.Dyadic
open import RealTheory.Completion

DReal : Set
DReal = C Dyadic
{-# COMPILE AGDA2HS DReal #-}
