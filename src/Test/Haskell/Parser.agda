-- Some tests for checking the correctness of the parser
-- with the QuickCheck Haskell library.
-- Closely based on Test.Parser.
-- Incomplete; this is now mainly for the purpose of demonstrating
-- how it could look like.

-- NOTE: this is not working yet (the tests fail),
-- but the concept can be seen from it.

{-# OPTIONS --erasure #-}
module Test.Haskell.Parser where
{-# FOREIGN AGDA2HS {-# LANGUAGE StandaloneDeriving #-} #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_==_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Int
open import Agda.Builtin.Char
open import Haskell.Prim.Tuple
open import Haskell.Prim.Either
open import Haskell.Prim.String
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Show
open import Haskell.Prim.List
open import Haskell.Prim.Ord
open import Haskell.Prim.Applicative
open import Haskell.Prim using
    (Bool; True; False; List; []; _∷_; fromString; IsTrue; if_then_else_; _$_; _∘_)

open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import RealTheory.AppRational
open import RealTheory.Completion
open import HaskellInstance.Eq

open import Shell.Parser
open import Shell.Exp
open import Shell.Statement

{-# FOREIGN AGDA2HS
import Test.QuickCheck

import Prelude (Show, Bool(..), Either(..), show, IO, String, ($), (+), (++), Ord(..), (&&),
                  (<$>), (/=), Monad(..), Applicative(..), abs, (.), ceiling, sqrt, fromIntegral)

import Implementation.Frac
import Implementation.Rational
import HaskellInstance.Show
import HaskellInstance.Eq
#-}


{-# FOREIGN AGDA2HS
-- We need an Arbitrary instance for the naturals.
instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink = shrinkIntegral
#-}

-- Actually, we can write the functions themselves in Agda.

-- For the natural parser:
prop_naturalCorrect : Nat -> Bool
prop_naturalCorrect n =
  runParser natural (show n) == Right (n , "")
{-# COMPILE AGDA2HS prop_naturalCorrect #-}

{-# FOREIGN AGDA2HS
-- We need some generators here.
instance Arbitrary Rational where
  arbitrary = do
    num <- arbitrary
    den <- arbitrary `suchThat` (/=0)
    return (MkFrac num den)

-- Now, we need a syntax tree generator.
-- Beware: this might not be semantically correct
-- (e.g. it might try to subtract bools).
-- The chance of generating a leaf
-- will decrease as O(1/√n).
instance Arbitrary Exp where
  arbitrary =               -- v we must ensure it is not zero
    sized $ \n -> let sn = max 1 $ fromIntegral $ ceiling $ sqrt $ fromIntegral n;
                      smallArbitrary = (resize sn arbitrary :: Gen Exp) in
    frequency
      [ (5, BoolLit <$> arbitrary)
      , (5, IntLit  <$> arbitrary)
      -- We take this out as it confuses Eq
      -- (it would be parsed as Div).
      -- , (5, RatLit  <$> arbitrary)
      , (5, return Pi)
      , (5, return E)
      -- this does not like Unicode
      , (5, Var     <$> oneof [return "x", return "y", return "verylongname", return "res"])
      , (5, History <$> arbitrary)
      -- these were the leaves;
      -- now come the inner nodes
      -- with a higher probability
      , (n, Neg     <$> smallArbitrary)
      , (n, Not     <$> smallArbitrary)
      , (n, Pow     <$> smallArbitrary <*> smallArbitrary)
      , (n, Pow     <$> smallArbitrary <*> smallArbitrary)
      , (n, Div     <$> smallArbitrary <*> smallArbitrary)
      , (n, Mul     <$> smallArbitrary <*> smallArbitrary)
      , (n, Sub     <$> smallArbitrary <*> smallArbitrary)
      , (n, Add     <$> smallArbitrary <*> smallArbitrary)
      , (n, Lt      <$> smallArbitrary <*> smallArbitrary)
      , (n, Le      <$> smallArbitrary <*> smallArbitrary)
      , (n, Eq      <$> smallArbitrary <*> smallArbitrary)
      , (n, And     <$> smallArbitrary <*> smallArbitrary)
      , (n, Or      <$> smallArbitrary <*> smallArbitrary)
      , (n, Expo    <$> smallArbitrary)
      , (n, Sin     <$> smallArbitrary)
      , (n, Cos     <$> smallArbitrary)
      , (n, Sqrt    <$> smallArbitrary)
      ]
#-}

-- Returns the precedence level of the top operator in the syntax tree.
-- Precedences are based on those in Haskell.
-- Atomics have an infinite precedence.
precedence : Exp -> Nat
precedence (BoolLit x) = 100
precedence (IntLit x) = 100
precedence (RatLit x) = 100
precedence (Var x) = 100
precedence (History x) = 100 -- for now, at least
precedence (Neg x) = 9
precedence (Not x) = 5
precedence (Pow x x₁) = 8
precedence (Div x x₁) = 7
precedence (Mul x x₁) = 7
precedence (Sub x x₁) = 6
precedence (Add x x₁) = 6
precedence (Lt x x₁) = 4
precedence (Le x x₁) = 4
precedence (Exp.Eq x x₁) = 4
precedence (And x x₁) = 3
precedence (Or x x₁) = 2
precedence Pi = 100
precedence E = 100
precedence (Expo x) = 10
precedence (Sin x) = 10
precedence (Cos x) = 10
precedence (Sqrt x) = 10
{-# COMPILE AGDA2HS precedence #-}

-- This drops one space (if there is one) from the beginning of a string.
dropOneSpace : String -> String
dropOneSpace (' ' ∷ xs) = xs
dropOneSpace xs         = xs
{-# COMPILE AGDA2HS dropOneSpace #-}

-- Puts brackets at the ends of a string.
-- Also calls dropOneSpace.
bracket : String -> String
bracket str = "(" ++ dropOneSpace str ++ ")"
{-# COMPILE AGDA2HS bracket #-}

expToString' : Exp -> String

-- Helper functions for expToString'.
private
  -- outer precedence, inner expression, operator
  prefix : Nat -> Exp -> String -> String
  prefix prec inner op = if prec > precedence inner
                           then op ++ bracket (expToString' inner)
                           else op ++ ' ' ∷ (expToString' inner)
  {-# COMPILE AGDA2HS prefix #-}

  -- outer precedence, left child, right child, operator
  infixl' : Nat -> Exp -> Exp -> String -> String
  infixl' prec left right op = (if prec > precedence left
                                  then bracket (expToString' left)
                                  else expToString' left)
                               ++ " " ++ op ++ " " ++ 
                               (if prec >= precedence right
                                  then bracket (expToString' right)
                                  else expToString' right)
  {-# COMPILE AGDA2HS infixl' #-}

  -- similarly
  -- note the different usage of _>=_ and _>_
  -- outer precedence, left child, right child, operator
  infixr' : Nat -> Exp -> Exp -> String -> String
  infixr' prec left right op = (if prec >= precedence left
                                  then bracket (expToString' left)
                                  else expToString' left)
                               ++ " " ++ op ++ " " ++ 
                               (if prec > precedence right
                                  then bracket (expToString' right)
                                  else expToString' right)
  {-# COMPILE AGDA2HS infixr' #-}

  -- for named functions
  -- inner expression and name
  namedFunction : Exp -> String -> String
  namedFunction inner name = " " ++ name ++ bracket (expToString' inner)
  {-# COMPILE AGDA2HS namedFunction #-}

-- And we also have to write a function which converts syntax trees back to strings,
-- with as few brackets as possible.
-- Beware: this might have whitespace at the beginning!
-- (A randomly generated string would hardly be parsable.)
-- We have to consider precedence levels.
-- expToString' : Exp -> String
expToString' (BoolLit x) = show x
expToString' (IntLit x) = show x
expToString' (RatLit x) = '(' ∷ show (num x) ++ '/' ∷ show (den x) ++ ")" 
expToString' (Var x) = ' ' ∷ x
expToString' (History x) = " history[" ++ show x ++ "]"
expToString' (Neg inner) = prefix 9 inner "-"
expToString' (Not inner) = prefix 4 inner "!"
expToString' (Pow left right) = infixr' 8 left right "^"
expToString' (Div left right) = infixl' 7 left right "/"
expToString' (Mul left right) = infixl' 7 left right "*"
expToString' (Sub left right) = infixl' 6 left right "-"
expToString' (Add left right) = infixl' 6 left right "+"
-- some are actually infix (neither infixl nor infixr)
-- but for the sake of simplicity:
expToString' (Lt left right) = infixl' 4 left right "<"
expToString' (Le left right) = infixl' 4 left right "<="
expToString' (Exp.Eq left right) = infixl' 4 left right "=="
expToString' (And left right) = infixr' 3 left right "&&"
expToString' (Or left right) = infixr' 2 left right "||"
expToString' Pi = " pi"
expToString' E = " e"
expToString' (Expo inner) = namedFunction inner "exp"
expToString' (Sin inner) = namedFunction inner "sin"
expToString' (Cos inner) = namedFunction inner "cos"
expToString' (Sqrt inner) = namedFunction inner "sqrt"
{-# COMPILE AGDA2HS expToString' #-}

-- This drops the space (if there is one) from the beginning of the string
-- returned by expToString'.
expToString : Exp -> String
expToString = dropOneSpace ∘ expToString'
{-# COMPILE AGDA2HS expToString #-}

{-
-- Actually, we could once write an ultimate proof
-- (but C-u C-u C-c C_, hangs; so it is probably too much for it
-- unless we write it on paper):
@0 pExpCorrect : ∀ (exp : Exp) -> runParser pExp (expToString exp) ≡ Right (exp , "")
-- Literals are hard to check because of the builtin show functions.
pExpCorrect (BoolLit x) = {!!}
pExpCorrect (IntLit x) = {!!}
pExpCorrect (RatLit x) = {!!}
pExpCorrect (Var x) = {!!}
pExpCorrect (History x) = {!!}
pExpCorrect (Neg exp) = {!!}
pExpCorrect (Not exp) = {!!}
pExpCorrect (Pow exp exp₁) = {!!}
pExpCorrect (Div exp exp₁) = {!!}
pExpCorrect (Mul exp exp₁) = {!!}
pExpCorrect (Sub exp exp₁) = {!!}
pExpCorrect (Add exp exp₁) = {!!}
pExpCorrect (Lt exp exp₁) = {!!}
pExpCorrect (Le exp exp₁) = {!!}
pExpCorrect (Exp.Eq exp exp₁) = {!!}
pExpCorrect (And exp exp₁) = {!!}
pExpCorrect (Or exp exp₁) = {!!}
pExpCorrect Pi = {!!}
pExpCorrect E = {!!}
pExpCorrect (Expo exp) = {!!}
pExpCorrect (Sin exp) = {!!}
pExpCorrect (Cos exp) = {!!}
pExpCorrect (Sqrt exp) = {!!}
-}

-- And now, we can start writing tests.

-- For the unary not (!) operator:
prop_notCorrect : Exp -> Bool
prop_notCorrect exp = (λ {(Right (Not exp' , _)) -> exp == exp'; _ -> False})
                         $ runParser pExp (expToString (Not exp))
{-# COMPILE AGDA2HS prop_notCorrect #-}

-- For a binary operator:
prop_addCorrect : Exp -> Exp -> Bool
prop_addCorrect left right = (λ {(Right (Add left' right' , _)) -> left == left' && right == right'; _ -> False})
                                $ runParser pExp (expToString (Add left right))
{-# COMPILE AGDA2HS prop_addCorrect #-}

-- It can similarly be solved for statement syntax.

-- And full test cases:
prop_fullCorrect : Exp -> Bool
prop_fullCorrect exp = (λ {(Right (exp' , _)) -> exp == exp'; _ -> False})
                          $ runParser pExp (expToString exp)
{-# COMPILE AGDA2HS prop_fullCorrect #-}

{-# FOREIGN AGDA2HS
-- We need this:
deriving instance Show Exp

-- This contains all the propositions we would like to test.
-- Actually, this will be called by main.
parserTestAll :: IO ()
parserTestAll = do
  quickCheck prop_naturalCorrect
  quickCheckWith stdArgs{maxSize = 10} prop_notCorrect
  quickCheckWith stdArgs{maxSize = 10} prop_addCorrect
  quickCheckWith stdArgs{maxSize = 10} prop_fullCorrect
#-}

