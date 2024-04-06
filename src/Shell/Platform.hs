-- This is only written in Haskell
-- as agda2hs does not really like the C preprocessor.
{-# LANGUAGE CPP #-}

#ifdef mingw32_HOST_OS
module Shell.Platform (module Shell.Platform.Win32) where
import Shell.Platform.Win32
#else
#if defined(linux_HOST_OS) || defined(darwin_HOST_OS)
module Shell.Platform (module Shell.Platform.Posix) where
import Shell.Platform.Win32
#endif
#endif
