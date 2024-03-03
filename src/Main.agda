-- A main program for a simple interpreter.
{-# OPTIONS --erasure --guardedness #-}

module Main where

-- We put the shell modules here too
-- so that they get compiled by agda2hs.

import Shell.CalcState
import Shell.Interaction

{-# FOREIGN AGDA2HS

import Data.Text (unpack, strip, pack)
import System.IO

import Implementation.Dyadic
import RealTheory.AppRational
import RealTheory.Completion
import Shell.CalcState
import Shell.Interaction

main :: IO ()
main = do
  putStrLn "Welcome to the AcornShell interpreter.\nType \":q\" to quit."
  calcState <- emptyCalcState
  (prompt :: CalcState (C Dyadic) -> IO ()) calcState

prompt :: AppRational aq => CalcState (C aq) -> IO ()
prompt calcState = do
  putStr "acorn> "
  hFlush stdout   -- so that it gets printed immediately
  command <- (unpack . strip . pack) <$> getLine
  if command == ":q"
  then return ()
  else do
    answer <- execCommand' calcState command 100
    putStrLn answer
    prompt calcState

#-}
