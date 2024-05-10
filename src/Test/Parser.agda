-- Some tests for checking the correctness of the parser
-- when proofs are not available.
-- Incomplete; this is now mainly for the purpose of demonstrating
-- how it could look like.
{-# OPTIONS --erasure #-}
module Test.Parser where

open import Tool.Cheat

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Int
open import Agda.Builtin.Char
open import Haskell.Prim.Either
open import Haskell.Prim.Tuple
open import Haskell.Prim.String
open import Haskell.Prim.Show
open import Haskell.Prim.List
open import Haskell.Prim using (List; True; False; []; _∷_; fromString; IsTrue)

open import Implementation.Nat

open import Shell.Parser
open import Shell.Exp
open import Shell.Statement
open import Test.Haskell.Parser using (bracket)

-- First idea:
-- we already write it with the general type signature,
-- but only prove it for the test cases we wish
-- and cheat away the rest.

-- show calls on primShowNat, which cannot really be resolved...
-- it's an Agda builtin.
-- But that could be circumvented by defining a "normal" Agda function
-- and postulating that it is equal to primShowNat.
-- It could be done similarly to all the others.
{-# TERMINATING #-} -- for now
@0 showNat : Nat -> String
showNat zero = "0"
showNat (suc n-1) = showNatAux (suc n-1) -- this is different in printing "" for 0
  where
  showNatAux : Nat -> String
  showNatAux 0 = ""
  showNatAux (suc n-1) = let n = suc n-1 in
      showNatAux (natDiv n 10 tt) ++ showDigit (natMod n 10 tt) cheat ∷ []
    where
    showDigit : (k : Nat) -> .(IsTrue (k < 10)) -> Char
    showDigit zero _ = '0'
    showDigit (suc zero) _ = '1'
    showDigit (suc (suc zero)) _ = '2'
    showDigit (suc (suc (suc zero))) _ = '3'
    showDigit (suc (suc (suc (suc zero)))) _ = '4'
    showDigit (suc (suc (suc (suc (suc zero))))) _ = '5'
    showDigit (suc (suc (suc (suc (suc (suc zero)))))) _ = '6'
    showDigit (suc (suc (suc (suc (suc (suc (suc zero))))))) _ = '7'
    showDigit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) _ = '8'
    showDigit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) _ = '9'

-- Now some test cases.
@0 showNatTest : ∀ (n : Nat) -> showNat n ≡ show n
showNatTest 0 = refl
showNatTest 1 = refl
showNatTest 2 = refl
showNatTest 9 = refl
showNatTest 10 = refl
showNatTest 20 = cheat
-- showNatTest 21 = {!!}
showNatTest n = cheat
-- The problem: any pattern matching with a literal greater than 20
-- fails with:
-- "Matching on natural number literals is done by expanding the
-- literal to the corresponding constructor pattern, so you probably
-- don't want to do it this way."

-- So, we have to include some larger test cases separately as well.
@0 naturalTest21 : showNat 21 ≡ show 21
naturalTest21 = refl
@0 naturalTest2109 : showNat 2109 ≡ show 2109
naturalTest2109 = refl

-- And after this, we cannot really do more than postulate the equivalence
-- of the two.
postulate
  @0 showNatPost : ∀ (n : Nat) -> showNat n ≡ show n

-- After this, we can use showNat in the proofs.
@0 naturalProof : ∀ (n : Nat) -> runParser natural (showNat n) ≡ Right (n , "")
naturalProof zero = refl
naturalProof (suc zero) = refl
naturalProof (suc (suc n)) = cheat    -- we will finish that sometime...
                                      -- we would need more additional proofs
                                      -- from earlier levels

-- This would be the idea for a proof for a prefix operator;
-- but here, C-c C-, hangs.
-- We do not have to consider precedences;
-- it's enough to call the appropriate parser.
@0 notProof : ∀ (str : String) (exp : Exp)
                -> runParser pRealFun str ≡ Right (exp , "")
                -> runParser pNot ('!' ∷ str) ≡ Right (Not exp , "")
-- Sadly, this only works with list syntax.
-- But the additional advantage is that we also test the other parsers
-- with these cases.
notProof ('T' ∷ 'r' ∷ 'u' ∷ 'e' ∷ []) (BoolLit True) refl = refl
notProof ('(' ∷ 'x' ∷ '&' ∷ '&' ∷ ' ' ∷ 'y' ∷ ')' ∷ [])
         (And (Var ('x' ∷ [])) (Var ('y' ∷ [])))
         refl = refl
notProof str exp hyp = cheat

-- For a binary operator:
@0 addProof : ∀ (str1 str2 : String) (exp1 exp2 : Exp)
                -> runParser pAddSub str1 ≡ Right (exp1 , "")
                -> runParser pAddSub str2 ≡ Right (exp2 , "")
                -> runParser pExp (bracket str1 ++ '+' ∷ bracket str2) ≡ Right (Add exp1 exp2 , "")
addProof ('1' ∷ '-' ∷ '2' ∷ [])
         ('3' ∷ '-' ∷ '4' ∷ [])
         (Sub (NatLit 1) (NatLit 2))
         (Sub (NatLit 3) (NatLit 4))
         refl refl = refl
-- this shall not work, as pSub must not be able to parse it without brackets
-- but it is not; so this is fine
{-
addProof ('1' ∷ '+' ∷ '2' ∷ [])
         ('3' ∷ '+' ∷ '4' ∷ [])
         (Add (IntLit (pos 1)) (IntLit (pos 2)))
         (Add (IntLit (pos 3)) (IntLit (pos 4)))
         e1 e2 = {!!}
-}
addProof str1 str2 exp1 exp2 e1 e2 = cheat

-- For statement syntax:
@0 ifProof : ∀ (condStr progStr : String)
               (condExp : Exp)
               (program : List Statement)
                   -> runParser pExp condStr ≡ Right (condExp , "")
                   -> runParser pProgram progStr ≡ Right (program , "")
                   -> runParser pStatement ("if " ++ condStr ++ '{' ∷ progStr ++ "}")
                                ≡ Right (If condExp program , "")
ifProof ('3' ∷ '=' ∷ '=' ∷ '5' ∷ [])
        ('t' ∷ '=' ∷ '5' ∷ ';' ∷ 't' ∷ '=' ∷ 't' ∷ '-' ∷ '1' ∷ [])
        (Eq (NatLit 3) (NatLit 5))
        (Assign ('t' ∷ []) (NatLit 5) ∷ Assign ('t' ∷ []) (Sub (Var ('t' ∷ [])) (NatLit 1)) ∷ [])
        refl refl = refl
ifProof condStr progStr condExp program hyp1 hyp2 = cheat

-- And finally, some full test cases.
-- Here, the examples themselves are in the type signature;
-- so we don't need to pattern match with _∷_.
-- A general proof could only be added
-- if we wrote something like a Show instance for a syntax tree;
-- then, we could prove something like
-- ∀ {real : Set} (program : List (Statement real)) -> runParser pProgram (show program) ≡ Right (program , "").

@0 fullTest1 : ∀ {real : Set} ->
                runParser pExp "3 - sin(pi) * 5 "
                  ≡ Right (Sub (NatLit 3) (Mul (Sin Pi) (NatLit 5)) , "")
fullTest1 = refl
@0 fullTest2 : ∀ {real : Set} ->
                runParser pProgram "if (3 == 3) {t = 3 - sin(pi) * 5; t}; while (5 <= 4) {}"
                  ≡ Right (If (Eq (NatLit 3) (NatLit 3))
                              (Assign "t" (Sub (NatLit 3) (Mul (Sin Pi) (NatLit 5))) ∷ Eval (Var "t") ∷ [])
                           ∷ While (Le (NatLit 5) (NatLit 4))
                                    (Empty ∷ [])
                           ∷ []
                           , "")
fullTest2 = refl
