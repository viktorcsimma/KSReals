-- A data type which will contain
-- variables and history
-- in a mutable form.
-- A pointer to it will be passed to C++.
{-# OPTIONS --erasure --guardedness #-}


module Shell.CalcState where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List
open import Agda.Builtin.FromString
open import Haskell.Prim.Bool
open import Haskell.Prim.Maybe
open import Haskell.Prim.List
open import Haskell.Prim.Either
open import Haskell.Prim.String
open import Haskell.Prim.Show
import Haskell.Data.Map as Map
open import Haskell.Prim.Ord
open import Haskell.Prim.Monad
open Do
open import Haskell.Prim using (if_then_else_; case_of_; _$_; a)

open import Tool.Cheat

open import Tool.ErasureProduct using (_:&:_)
open import Algebra.SemiRing
open import Algebra.Ring
open import Algebra.Field
open import Operator.Cast
open import Operator.Decidable
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Implementation.Rational
open import RealTheory.AppRational
open import RealTheory.Completion
open import RealTheory.Real
import RealTheory.Instance.Cast
open import Function.Exp
open import Function.Trigonometric
open import Function.SquareRoot

open import Shell.Value
open import Shell.Exp

-- The foreign Haskell code depends on them;
-- this helps agda2hs know they also need to be compiled.
import Shell.Statement
import Shell.Parser

{-# FOREIGN AGDA2HS
import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.IORef

import Algebra.SemiRing
import RealTheory.Instance.Cast

import Shell.Exp
import Shell.Value
import Shell.Statement
import Shell.Parser

import Prelude hiding (Num, lookup, insert, (+), (-), (*), (/), negate, recip, Rational, sin, cos, null, exp, pi)
#-}

-- For storing variables.
Variables : Set -> Set
Variables real = Map.Map String (Value real)
{-# COMPILE AGDA2HS Variables #-}
-- For storing the results of past queries
-- (last in, first out).
PastResults : Set -> Set
PastResults real = List (Value real) -- we only need the values;
{-# COMPILE AGDA2HS PastResults #-}  -- the queries will be stored on the C++ side

-- Returns the element at a given natural index in a Just,
-- or Nothing if it is out of bounds.
atMaybe : List a -> Nat -> Maybe a
atMaybe [] _ = Nothing
atMaybe (x ∷ xs) n = if (n ≃# 0) then Just x else atMaybe xs (n Agda.Builtin.Nat.- 1)
-- yes, this is ugly; but that's how agda2hs accepts it
{-# COMPILE AGDA2HS atMaybe #-}

-- A helper for conversions.
multRatReal : {aq : Set} {{araq : AppRational aq}} ->
        Rational -> C aq -> C aq
multRatReal (MkFrac n d denNotNull) x = multByAQ (cast n) (x * recip (cast n) cheat)
{-# COMPILE AGDA2HS multRatReal #-}

-- Performs logical operations on values.
-- Called by evalExp'.
logopVal : {real : Set} -> (Bool -> Bool -> Bool) -> Value real -> Value real -> Either String (Value real)
logopVal f val1 val2 =
  case val1 of λ where
    (VBool b1) → case val2 of λ where
      (VBool b2) → Right $ VBool $ f b1 b2
      _ -> Left "logical operators are only applicable to booleans"
    _ -> Left "logical operators are only applicable to booleans"
{-# COMPILE AGDA2HS logopVal #-}

-- Returns the value of an expression
-- (or an error message)
-- without side effects.
-- Written in Agda so that the legality of the operations can be proven.

evalExp' : {aq : Set} {{araq : AppRational aq}} ->
        Variables (C aq) -> PastResults (C aq) -> Exp (C aq) -> Either String (Value (C aq))
evalExp' _ _ (BoolLit b) = Right (VBool b)
evalExp' _ _ (IntLit i)  = Right (VInt i)
evalExp' _ _ (RatLit q)  = Right (VRat q)
evalExp' _ _ (RealLit x) = Right (VReal x)
evalExp' _ _ Pi          = Right (VReal pi)
evalExp' _ _ E           = Right (VReal e)
evalExp' vars _ (Var name)  =
  case (Map.lookup name vars) of λ where
    (Just val) -> Right val
    Nothing  -> Left (name ++ fromString " is undefined")
-- Now a bit of safe indexing. (i is Natural.)
evalExp' _ hist (History i) =
  case atMaybe hist i of λ where
    Nothing -> Left ("index " ++ show i ++ " is too large")
    (Just res) -> Right res
evalExp' vars hist (Neg exp) = do  -- use Either as a monad
  val <- evalExp' vars hist exp
  case val of λ where
    (VInt i) -> Right $ VInt (negate i)
    (VRat q) -> Right $ VRat (negate q)
    (VReal x) -> Right $ VReal (negate x)
    _      -> Left "operator '-' is not applicable to booleans"
evalExp' vars hist (Expo expr) = do
  val <- evalExp' vars hist expr
  case val of λ where
    (VBool _) -> Left "function \"exp\" is not applicable to booleans"
    (VInt n)  -> Right $ VReal $ expQ (cast n)
    (VRat (MkFrac k d dNotNull))  -> Right $ VReal $ exp (multByAQ (cast k) (recip (cast d) cheat))
                                                  -- ^ TODO: implement this for Frac aq!
    (VReal x) -> Right $ VReal $ exp x
evalExp' vars hist (Sin exp) = do
  val <- evalExp' vars hist exp
  case val of λ where
    (VBool _) -> Left "function \"sin\" is not applicable to booleans"
    (VInt n)  -> Right $ VReal $ sinQ (cast n)
    (VRat (MkFrac k d dNotNull))  -> Right $ VReal $ sinFracQ (MkFrac (cast k) (cast d) cheat)
    (VReal x) -> Right $ VReal $ sin x
evalExp' vars hist (Cos exp) = do
  val <- evalExp' vars hist exp
  case val of λ where
    (VBool _) -> Left "function \"cos\" is not applicable to booleans"
    (VInt n)  -> Right $ VReal $ cosQ (cast n)
    (VRat (MkFrac k d dNotNull))  -> Right $ VReal $ cosFracQ (MkFrac (cast k) (cast d) cheat)
    (VReal x) -> Right $ VReal $ cos x
evalExp' vars hist (Sqrt exp) = do
  val <- evalExp' vars hist exp
  case val of λ where
    (VBool _) -> Left "function \"sqrt\" is not applicable to booleans"
    (VInt n)  -> if (n <# pos 0) then Left "square root of negative integer"
                                 else Right $ VReal $ sqrtQ (cast n :&: cheat)
    (VRat (MkFrac k d dNotNull))
        -> if (MkFrac k d dNotNull) <# Algebra.SemiRing.null
             then Left "square root of negative rational"
             else Right $ VReal $ sin (multByAQ (cast k) (recip (cast d) cheat))
                                    -- ^ TODO: implement this for Frac aq!
    (VReal x) -> Left "cannot decide sign of real for sqrt (coming soon)"
evalExp' vars hist (Not exp) = do
  val <- evalExp' vars hist exp
  case val of λ where
    (VBool b) -> Right $ VBool (not b)
    _       -> Left "operator '!' is not applicable to numbers"
evalExp' vars hist (Div exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "operator '/' is not applicable to booleans"
  let int0 = "division by integer 0"
  let rat0 = "division by rational 0"
  let realden = "can't decide whether real denominator is 0 (coming soon)"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt (pos 0)) -> Left int0
      (VInt d) -> Right $ VRat (MkFrac n d cheat)
      (VRat (MkFrac (pos 0) _ _)) -> Left rat0
      (VRat (MkFrac k d _)) -> Right $ VRat (MkFrac (n * d) k cheat)
      (VReal x) -> Left realden
    (VRat (MkFrac k d dNotNull)) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt (pos 0)) -> Left int0
      (VInt n) -> Right $ VRat (MkFrac k (d * n) cheat)
      (VRat (MkFrac (pos 0) _ _)) -> Left rat0
      (VRat (MkFrac k2 d2 _)) -> Right $ VRat (MkFrac (k * d2) (k2 * d) cheat)
      (VReal x) -> Left realden
    (VReal x) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt (pos 0)) -> Left int0
      (VInt n) -> Right $ VReal $ x * recip (returnC (cast n)) cheat
                                   -- ^ it might not be converted to Dyadic;
                                   -- that's why we do it like this
      (VRat (MkFrac (pos 0) _ _)) -> Left rat0
      (VRat (MkFrac k2 d2 _)) ->
          Right $ VReal $ multRatReal (MkFrac d2 k2 cheat) x
      (VReal x) -> Left realden
evalExp' vars hist (Mul exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "operator '*' is not applicable to booleans"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt m) -> Right $ VInt (n * m)
      (VRat (MkFrac k d dNotNull)) -> Right $ VRat (MkFrac (n * k) d dNotNull)
      (VReal x) -> Right $ VReal $ multByAQ (cast n) x
    (VRat (MkFrac k d dNotNull)) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VRat $ MkFrac (k * n) d dNotNull
      (VRat (MkFrac k2 d2 d2NotNull)) -> Right $ VRat $ MkFrac (k * k2) (d * d2) cheat
      (VReal x) -> Right $ VReal $ multRatReal (MkFrac k d dNotNull) x
    (VReal x) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VReal $ multByAQ (cast n) x
      (VRat q) -> Right $ VReal $ multRatReal q x
      (VReal x2) -> Right $ VReal $ x * x2
evalExp' vars hist (Sub exp1 exp2) = do
  -- we are not doing a shortcut here
  -- so that we don't antagonise the termination checker
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "operator '-' is not applicable to booleans"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt m) -> Right $ VInt (n - m)
      (VRat q) -> Right $ VRat $ cast n - q
      (VReal x) -> Right $ VReal $ addAQ (cast n) (negate x)
    (VRat q) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VRat $ q - cast n
      (VRat q2) -> Right $ VRat $ q - q2
      (VReal x) -> Right $ VReal $ cast q - x
    (VReal x) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VReal $ addAQ (cast (negate n)) x
      (VRat q) -> Right $ VReal $ x - cast q
      (VReal x2) -> Right $ VReal $ x - x2
evalExp' vars hist (Add exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "operator '+' is not applicable to booleans"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt m) -> Right $ VInt (n + m)
      (VRat q) -> Right $ VRat $ cast n + q
      (VReal x) -> Right $ VReal $ addAQ (cast n) x
    (VRat q) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VRat $ q + cast n
      (VRat q2) -> Right $ VRat $ q + q2
      (VReal x) -> Right $ VReal $ cast q + x
    (VReal x) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VReal $ addAQ (cast n) x
      (VRat q) -> Right $ VReal $ x + cast q
      (VReal x2) -> Right $ VReal $ x + x2
-- I've tried to generalise this, but the compiler got "__IMPOSSIBLE_VERBOSE__" from it.
-- So now, it's code duplication.
evalExp' vars hist (Lt exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "logical comparison is not applicable to booleans"
  let noReal = "tried to perform logical comparison on reals (coming soon)"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n2) -> Right $ VBool $ n <# n2
      (VRat q)  -> Right $ VBool $ cast n <# q
      (VReal _) -> Left noReal
    (VRat q) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VBool $ q <# cast n
      (VRat q2)  -> Right $ VBool $ q <# q2
      (VReal _) -> Left noReal
    (VReal _) -> Left noReal
evalExp' vars hist (Le exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "logical comparison is not applicable to booleans"
  let noReal = "tried to perform logical comparison on reals (coming soon)"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n2) -> Right $ VBool $ n ≤# n2
      (VRat q)  -> Right $ VBool $ cast n ≤# q
      (VReal _) -> Left noReal
    (VRat q) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VBool $ q ≤# cast n
      (VRat q2)  -> Right $ VBool $ q ≤# q2
      (VReal _) -> Left noReal
    (VReal _) -> Left noReal
evalExp' vars hist (Eq exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  let noBool = "logical comparison is not applicable to booleans"
  let noReal = "tried to perform logical comparison on reals (coming soon)"
  case val1 of λ where
    (VBool _) -> Left noBool
    (VInt n) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n2) -> Right $ VBool $ n ≃# n2
      (VRat q)  -> Right $ VBool $ cast n ≃# q
      (VReal _) -> Left noReal
    (VRat q) -> case val2 of λ where
      (VBool _) -> Left noBool
      (VInt n) -> Right $ VBool $ q ≃# cast n
      (VRat q2)  -> Right $ VBool $ q ≃# q2
      (VReal _) -> Left noReal
    (VReal _) -> Left noReal
evalExp' vars hist (And exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  logopVal _&&_ val1 val2
evalExp' vars hist (Or exp1 exp2) = do
  val1 <- evalExp' vars hist exp1
  val2 <- evalExp' vars hist exp2
  logopVal _||_ val1 val2
{-# COMPILE AGDA2HS evalExp' #-}

{-# FOREIGN AGDA2HS
-- And now the Haskell-specific, side-effect-ridden side.

-- This has to be mutable,
-- because the C++ side will have a pointer
-- to the same instance
-- all the time.
-- That's why I cannot comfortably use
-- the State monad.
data CalcState real = MkCalcState
  { variables :: IORef (Variables real)
  , history   :: IORef (PastResults real)
  }

emptyCalcState :: IO (CalcState real)
emptyCalcState = do
  varsRef <- newIORef Map.empty
  histRef <- newIORef []
  return $ MkCalcState varsRef histRef

-- Returns the value of the variable "Ans",
-- wrapped in a Maybe.
-- It does not actually change the state.
maybeAns :: CalcState real -> IO (Maybe (Value real))
maybeAns (MkCalcState varsRef _) = do
  vars <- readIORef varsRef
  return (Map.lookup "Ans" vars)

-- Executes a statement and returns its result
-- (or an error message)
-- while modifying the CalcState accordingly.
-- When there is no other result,
-- it returns the value of the variable "Ans",
-- or if not even that exists, an integer 0.
-- Beware: for complex statements (e.g. an if or a while statement),
-- it might modify variables even if it fails!
execStatement :: AppRational aq =>
    CalcState (C aq) -> Statement (C aq) -> IO (Either String (Value (C aq)))
execStatement calcState Empty = do
  ma <- maybeAns calcState
  case ma of
    Nothing  -> return $ Right (VInt 0)
    Just ans -> return $ Right ans
execStatement calcState (Eval exp) = do
  val <- evalExp calcState exp
  case val of                -- v "error while executing statement; "
    Left err -> return $ Left ("while evaluating expression: " ++ err)
    Right val -> do
      let varsRef = variables calcState; histRef = history calcState
      vars <- readIORef varsRef
      writeIORef varsRef (Map.insert "Ans" val vars)
      hist <- readIORef histRef
      writeIORef histRef (val : hist)
      return (Right val)
execStatement calcState (Assign name exp) = do
  val <- evalExp calcState exp
  case val of
    Left err -> return $ Left ("error while evaluating value to assign: " ++ err)
    Right val -> do
      let varsRef = variables calcState; histRef = history calcState
      vars <- readIORef varsRef
      writeIORef varsRef $ Map.insert "Ans" val (Map.insert name val vars) -- the only difference
      hist <- readIORef histRef
      writeIORef histRef (val : hist)
      return (Right val)
execStatement calcState (If cond program) = do
  cond <- evalExp calcState cond
  case cond of
    Left err -> return $ Left ("error while evaluating condition: " ++ err)
    Right (VBool False) -> execStatement calcState Empty
    Right (VBool True) -> execProgram calcState program
    _ -> return $ Left ("condition not a Boolean value")
execStatement calcState stmt@(While condExp program) = do
  cond <- evalExp calcState condExp
  case cond of
    Left err -> return $ Left ("error while evaluating condition: " ++ err)
    Right (VBool False) -> execStatement calcState Empty
    Right (VBool True) -> do
      res <- execProgram calcState program
      case res of
        left@(Left _) -> return left
        Right _ -> execStatement calcState stmt
    _ -> return $ Left ("condition not a Boolean value")

-- Executes a program (a list of statements)
-- and returns the result of the last statement.
-- Beware: for complex statements (e.g. an if or a while statement),
-- it might modify variables even if it fails!
execProgram :: AppRational aq =>
    CalcState (C aq) -> [Statement (C aq)] -> IO (Either String (Value (C aq)))
execProgram calcState [] = execStatement calcState Empty
execProgram calcState stmts =
  foldM execNext
        (Right (VInt 0)) -- this won't be used
        stmts
    where
      execNext left@(Left _) _ = return left  -- stop if there has already been an error
      execNext _ stmt = execStatement calcState stmt

-- Writes empty structures to both references.
clear :: CalcState real -> IO ()
clear (MkCalcState vars hist) = do
    writeIORef vars Map.empty
    writeIORef hist []

-- Evaluates an expression and return its value,
-- or an error message.
-- It does not modify the IORefs.
evalExp :: AppRational aq => CalcState (C aq) -> Exp (C aq) -> IO (Either String (Value (C aq)))
evalExp (MkCalcState vars hist) exp = do
    vars <- readIORef vars
    hist <- readIORef hist
    return $ evalExp' vars hist exp
#-}
