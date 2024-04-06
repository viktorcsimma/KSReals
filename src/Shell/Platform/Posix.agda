-- Implementation of platform-specific functions
-- for Unix-like systems.
module Shell.Platform.Posix where

{-# FOREIGN AGDA2HS

import Control.Concurrent
import System.Posix.Signals

-- Opens a new thread which is going to write its result into an MVar.
-- Also installs a signal handler for SIGINT
-- which stops the calculation thread and writes a default result
-- into the MVar, if triggered.
-- Since the signal handler only runs if there is a signal,
-- we don't need to worry about killing a "watcher thread".
runInterruptibly :: IO a -> a -> IO a
runInterruptibly action resultOnInterrupt = do
  mVar <- newEmptyMVar
  childThreadId <- forkIO (putMVar mVar =<< action)
  installHandler
    sigINT
    (CatchOnce $ killThread childThreadId >> putMVar mVar resultOnInterrupt)
    Nothing
  takeMVar mVar

#-}