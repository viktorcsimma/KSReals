# Acorn
**An agda2hs-compatible, verifiable representation of exact-real arithmetic
and a shell for playing with it.**

## Purpose

The goal of this library is to create an Agda implementation of exact real arithmetic
described by Krebbers and Spitters in 2013.
The library discussed is based on their mathematical foundations
and the concepts of the [CoRN](https://github.com/coq-community/corn/) analysis library
(which has been written in Coq).
However, it takes a new approach on the topic,
and aims to popularise the field of verified exact-real arithmetic
by _first_ showing a runnable representation,
with most proofs filled in only after this has been achieved.
The goal of full compatibility with the [agda2hs](https://github.com/agda/agda2hs) compiler
makes the code not only much more efficient,
but also easier to understand and use.
The familiar, Haskell-style environment of Agda,
combined with CoRN's type class-based algebraic operators
would allow users of the library
to get started quickly with writing useful software
based on reliable calculations
proven to be correct.

## Contents

The project has three outputs:
- a Haskell library made available through a Cabal package,
- an executable (`AcornShell`) that is a basic interpreter allowing you to try the library, and
- a foreign static library made available through a CMake package.

## Installation

First, you will need agda2hs.
Acorn does not get compiled with the vanilla version;
_you need a modified one_.
That is [commit a3c83ad](https://github.com/viktorcsimma/agda2hs/commit/a3c83ad3be876ce0c7aa31157f3107843bf2f465) on my fork.
(But hopefully, these changes will get merged soon.)
Clone it, check out the commit, then run `cabal install`.

### Cabal

Acorn is a full Cabal package.
When Cabal is run, the program in Setup.hs compiles the Agda sources
into the `hs` output directory;
the normal building process begins only then.

### CMake

For now, this has only been tested _on Ubuntu 20.04_.
But hopefully, I will make it work on Windows too.

For compiling a static library for use in C or C++,
use CMake:

```sh
cmake CMakeLists.txt
make all
sudo make install
```

The last command installs the library into a specific folder,
where it is globally available for all CMake projects.
With some strings attached.

On Ubuntu 20.04, the only way I could import it was this,
as CMake could not find it otherwise
(it forgot the `/usr/local/` from the beginning):

```cmake
include(GNUInstallDirs)
include(/usr/local/${CMAKE_INSTALL_LIBDIR}/cmake/Acorn/AcornTargets.cmake)
```

Of course, this is less-than-platform-independent.

Another caveat is that you need to pass some specific options to the linker.
GHC links the Haskell RTS runtimes into the library, so we don't need to worry about that;
however, for some reason ld does not find system libraries by default.
The winning set for me (on Ubuntu) was this:

```cmake
target_link_options(calc PRIVATE -fuse-ld=gold -no-pie -fno-PIC -lstdc++ -ltinfo -lrt -lutil -ldl -lpthread -lgmp)
```

[Here](https://github.com/viktorcsimma/acorn-calc/blob/f9fac926687bf4cad252e3b55de27e62cfd3a9ee/CMakeLists.txt)
is an example CMakeLists.txt
for a test application `AcornCalc`
with source files `src/test.cpp` and `src/ViewModel/HsCalcStateWrapper.cpp`
and headers in the `include/` folder.

## Documentation

So far, a real documentation does not really exist.
The most detailed description about the library for now
is [this article](http://csimmaviktor.web.elte.hu/acorn.pdf)
But feel free to ask if you have questions.

## Contribution

Contributions are welcome!
