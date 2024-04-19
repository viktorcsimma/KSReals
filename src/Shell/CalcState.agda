-- A data type which will contain
-- variables and history
-- in a mutable form.
-- A pointer to it will be passed to C++.
-- This is actually written in Haskell.
{-# OPTIONS --erasure --guardedness #-}

module Shell.CalcState where

-- The foreign Haskell code depends on them;
-- this helps agda2hs know they also need to be compiled.
import Algebra.SemiRing
import RealTheory.Instance.Cast
import RealTheory.AppRational
import RealTheory.Completion
import Shell.Exp
import Shell.Value
import Shell.Statement
import Shell.Parser
import Shell.Evaluation

{-# FOREIGN AGDA2HS
import Control.Monad (foldM)
import qualified Data.Map as Map
import Data.IORef

import Algebra.SemiRing
import RealTheory.Instance.Cast
import RealTheory.AppRational
import RealTheory.Completion
import Shell.Exp
import Shell.Value
import Shell.Statement
import Shell.Parser
import Shell.Evaluation

import Prelude hiding (Num, lookup, insert, (+), (-), (*), (/), negate, recip, Rational, sin, cos, null, exp, pi)
#-}

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
