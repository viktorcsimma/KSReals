-- This is to run agda2hs
-- before compiling the generated Haskell modules.

import Distribution.Simple
import System.Process (callCommand)

main = defaultMainWithHooks simpleUserHooks { preBuild = prebuild }

prebuild args flags = do
  callCommand "agda2hs src/All.agda"
  preBuild simpleUserHooks args flags
