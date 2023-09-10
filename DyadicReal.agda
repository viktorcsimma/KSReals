-- A concrete implementation of the reals
-- based on dyadic rationals.

module DyadicReal where

open import AppRationals
open import Dyadic
open import Complete

DyadicReal : Set
DyadicReal = C Dyadic
{-# COMPILE AGDA2HS DyadicReal #-}
