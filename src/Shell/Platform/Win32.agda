-- Implementation of platform-specific functions
-- for Windows.

module Shell.Platform.Win32 where

{-# FOREIGN AGDA2HS {-# LANGUAGE ScopedTypeVariables #-} #-}

{-# FOREIGN AGDA2HS

import Control.Concurrent
import System.Win32.Event
import System.Win32.Process (sleep, iNFINITE)
import System.Win32.File (closeHandle)

-- Opens a new thread which is going to write its result into an MVar.
-- Also opens a "watcher thread"
-- which is going to wait on an event called "AcornInterruptEvent"
-- and if it is triggered, stops the calculation
-- and writes a Nothing into the MVar.
-- If the calculation runs successfully (so with Just sth),
-- the watcher thread is stopped by triggering the event;
-- if there is already a result in the MVar,
-- it does nothing.
-- The event is created by the watcher thread itself;
-- the "outer world" only needs to open it.
runInterruptibly :: IO a -> a -> IO a
runInterruptibly action resultOnInterrupt = do
  (mVar :: MVar (Maybe a)) <- newEmptyMVar
  childThreadId <- forkIO (putMVar mVar =<< (Just <$> action))
  watcherThreadId <- forkIO $ do
    -- an auto-reset event
    eventHandle <- createEvent Nothing False False "AcornInterruptEvent"
    waitResult <- waitForSingleObject eventHandle iNFINITE
    closeHandle eventHandle
    if waitResult == wAIT_OBJECT_0
      then do
        -- this will do nothing if the MVar has already been filled
        wasEmpty <- tryPutMVar mVar Nothing
        if wasEmpty
        then killThread childThreadId
        else return ()
      else
        error "waitResult failed"
  -- we only readMVar, so that it remains full
  -- and the watcher thread knows if there has been a result
  maybeResult <- readMVar mVar
  case maybeResult of
    Just result -> do
      -- stop the watcher thread by triggering the event
      ourEventHandle <- openEvent eVENT_MODIFY_STATE False "AcornInterruptEvent"
      setEvent ourEventHandle
      closeHandle ourEventHandle
      return result
    -- in this case, the watcher thread has already run
    -- and stopped the calculation thread
    Nothing -> return resultOnInterrupt

#-}