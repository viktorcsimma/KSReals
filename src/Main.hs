-- A main program for a simple interpreter.
-- This is needed to be written in Haskell;
-- otherwise, Cabal does not accept it.
module Main where

import Data.Char (isDigit)
import Data.List (isPrefixOf)
import Data.Text (unpack, strip, pack)
import System.IO

import Implementation.Dyadic
import RealTheory.AppRational
import RealTheory.Completion
import Shell.CalcState
import Shell.Interaction

import Control.Concurrent (myThreadId)
import Control.DeepSeq

-- The precision used at the start.
-- TODO: read this from command line arguments
defaultPrecision :: Int
defaultPrecision = 100

main :: IO ()
main = do
  putStrLn $ "Welcome to the AcornShell interpreter.\nThe default precision is " ++ show defaultPrecision ++ " digits (use \":setprec\" to change this).\nType \":q\" to quit."
  calcState <- emptyCalcState
  (prompt :: CalcState (C Dyadic) -> Int -> IO ()) calcState 100

-- the second parameter is the precision to apply
prompt :: (AppRational aq, NFData aq) => CalcState (C aq) -> Int -> IO ()
prompt calcState precision = do
  putStr "acorn> "
  hFlush stdout   -- so that it gets printed immediately
  command <- (unpack . strip . pack) <$> getLine
  if command == ":q"
  then return ()
  else if ":setprec " `isPrefixOf` command
  then do
    let num = (unpack . strip . pack) $ drop 9 command
    if all isDigit num
    then do
      -- call it with the new precision
      prompt calcState (read num)
    else do
      putStrLn "Invalid syntax for :setprec – have you written the number correctly?"
      prompt calcState precision
  else do
    answer <- execCommand' calcState command precision
    putStrLn answer
    prompt calcState precision
