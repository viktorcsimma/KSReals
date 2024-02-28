-- A module containing functions
-- for interacting with the interpreter
-- (a CalcState object).
-- The functions can also be used in C.
{-# OPTIONS --erasure #-}

module Shell.Interaction where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.FromString
open import Haskell.Prim.List using (_++_)
open import Haskell.Prim.String
open import Haskell.Prim.Show
open import Haskell.Prim using (_$_; the)

open import Tool.Cheat

open import Tool.ErasureProduct using (_:&:_)
open import HaskellInstance.Show
open import Algebra.SemiRing
open import Implementation.Nat
open import Implementation.Int
open import Implementation.Frac
open import Operator.Cast
open import Operator.Pow
open import RealTheory.AppRational
open import RealTheory.Completion
open import Shell.Value

{-# FOREIGN AGDA2HS

{-# LANGUAGE ForeignFunctionInterface #-}

import Prelude hiding (Rational)

import qualified Data.Map as Map
import Data.IORef
import Foreign.C.String
import Foreign.C.Types
import Foreign.StablePtr
import Numeric.Natural

import Tool.ErasureProduct
import HaskellInstance.Show
import Implementation.Dyadic
import Implementation.Frac
import Implementation.Rational
import RealTheory.AppRational
import RealTheory.Completion
import Shell.Exp
import Shell.Value
import Shell.Parser
import Shell.CalcState
#-}

-- Actually, some things can be written in Agda.

-- A helper for showValue
-- (otherwise, Haskell could not swallow `pos`).
fourtenprec : Nat -> Int
fourtenprec prec = pos $ 4 * 10 ^ prec
{-# FOREIGN AGDA2HS
fourtenprec :: Natural -> Integer
fourtenprec prec = 4 * 10 Prelude.^ prec
#-}

-- Returns a string representation of a value
-- with a given precision
-- (number of digits after the decimal point;
-- for now, this can only be natural because of the rational converter);
-- followed by " :: " and the type.
showValue : {aq : Set} {{ara : AppRational aq}} ->
    Value (C aq) -> Nat -> String
showValue (VBool b) _ = show b ++ " :: Bool"
showValue (VInt n)  _ = show n ++ " :: Integer"
showValue (VRat q)  prec = show (toDecimal q prec) ++ " :: Rational"
showValue (VReal x) prec = show (toDecimal
    (fun x $ _:&:_ (MkFrac (the Int one) (fourtenprec prec) cheat) cheat) prec)
                                       -- ^ for now, with a 0.25 precision and then rounding
                                       -- hopefully, that's enough
                                       -- (actually, if we knew, we would have a comparison algorithm)
                           ++ " :: Real"
{-# COMPILE AGDA2HS showValue #-}

{-# FOREIGN AGDA2HS

-- Initialises a CalcState
-- and returns a StablePtr to it.
initCalc :: IO (StablePtr (CalcState real))
initCalc = do
  varsRef <- newIORef Map.empty
  histRef <- newIORef []
  newStablePtr (MkCalcState varsRef histRef)
initCalcDyadic :: IO (StablePtr (CalcState (C Dyadic)))
initCalcDyadic = initCalc
foreign export ccall initCalcDyadic :: IO (StablePtr (CalcState (C Dyadic)))
initCalcRational :: IO (StablePtr (CalcState (C Rational)))
initCalcRational = initCalc
foreign export ccall initCalcRational :: IO (StablePtr (CalcState (C Rational)))

-- Executes a command given in a CString
-- with a given precision
-- and returns the result in a CString.
-- **Note: the C string must be freed on the C side!**
execCommand :: AppRational aq =>
    StablePtr (CalcState (C aq)) -> CString -> CInt -> IO CString
execCommand ptr cstr prec = do
  command <- peekCString cstr
  calcState <- deRefStablePtr ptr
  answer <- execCommand' calcState command (fromIntegral prec)
  newCString answer
-- We have to instantiate this with concrete types
-- in order to be able to export it.
execCommandDyadic :: StablePtr (CalcState (C Dyadic)) -> CString -> CInt -> IO CString
execCommandDyadic = execCommand
foreign export ccall execCommandDyadic
  :: StablePtr (CalcState (C Dyadic)) -> CString -> CInt -> IO CString
execCommandRational :: StablePtr (CalcState (C Rational)) -> CString -> CInt -> IO CString
execCommandRational = execCommand
foreign export ccall execCommandRational
  :: StablePtr (CalcState (C Rational)) -> CString -> CInt -> IO CString

-- Executes a command given in a String
-- with a given precision
-- and returns the result in a String.
-- Same as evalCommand, but without C types.
execCommand' :: AppRational aq =>
    CalcState (C aq) -> String -> Int -> IO String
execCommand' calcState command prec
  | prec < 0    = return $ "error: negative precision not yet supported"
  | otherwise   = do
    case runParser (topLevel pStatement) command of
      Left err -> return $ "error while parsing statement: " ++ err
      Right (stmt, _) -> do      
        result <- execStatement calcState stmt
        let answer = case result of {
          Left err -> "error while executing statement: " ++ err;
          Right val -> showValue val (fromIntegral prec)}
        return answer

-- Returns a new approximation of the result of the last successful command
-- with the given precision
-- (or 0, if none exists).
-- Note: the side effects do _not_ get executed again.
reevalCommand :: AppRational aq =>
    StablePtr (CalcState (C aq)) -> CInt -> IO CString
reevalCommand ptr prec = do
  calcState <- deRefStablePtr ptr
  mAns <- maybeAns calcState
  case mAns of
    Nothing -> newCString "0"
    Just val -> newCString $ showValue val (fromIntegral prec)

-- Frees the StablePtr pointing to the CalcState instance.
destructCalcDyadic :: StablePtr (CalcState (C Dyadic)) -> IO ()
destructCalcDyadic = freeStablePtr
foreign export ccall destructCalcDyadic :: StablePtr (CalcState (C Dyadic)) -> IO ()
destructCalcRational :: StablePtr (CalcState (C Rational)) -> IO ()
destructCalcRational = freeStablePtr
foreign export ccall destructCalcRational :: StablePtr (CalcState (C Rational)) -> IO ()

#-}
