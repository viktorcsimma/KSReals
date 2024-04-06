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

### Dependencies

#### zlib

You will need zlib1 to be able to install agda2hs
(see the [Agda documentation](https://agda.readthedocs.io/en/v2.5.4.1/getting-started/prerequisites.html)).
Otherwise, you will get an error message saying that zlib1 is missing
(well into the installation process).

On Windows, zlib1.dll can be installed this way:
- Install GHC through ghcup (you should probably do this anyway).
- Open the MinGW64 binary bundled with it (usually at `C:\ghcup\msys64\mingw64.exe`).
- In the shell appearing, type `pacman -S mingw-w64-x86_64-zlib`; this will install the zlib MinGW package.
- Now you will have `zlib1.dll` under `C:\ghcup\msys64\mingw64\bin`.
- Copy it into System32.
On Ubuntu/Debian; it should suffice to say `sudo apt install zlib1g-dev libncurses5-dev`.

#### agda2hs

Of course, you will need agda2hs.
Acorn does not get compiled with the vanilla version;
_you need a modified one_.
That is [commit a3c83ad](https://github.com/viktorcsimma/agda2hs/commit/a3c83ad3be876ce0c7aa31157f3107843bf2f465) on my fork.
(But hopefully, these changes will get merged soon.)
Clone it, check out the commit, then run `cabal install`.
_(If Cabal hangs on "Building Agda-2.x.x...", you can try pressing Control-C;
once, it magically proceeded with the installation then.)_

If this is done, add the Cabal binary path
(usually `~/.cabal/bin/` on Unix and `C:\cabal\bin\` on Windows)
to the PATH variable
so that the command interpreter sees and recognises agda2hs.

Lastly, in order to make Agda see the agda2hs standard library,
add the path to the `agda2hs.agda-lib` file in the project root
(e.g. `C:\path\to\agda2hs\agda2hs.agda-lib` on Windows)
to Agda's global library list.
agda2hs will tell you where it is when you try to run it on `src/All.agda`
(on Windows, it was `AppData\Roaming\agda\libraries` for me;
but I had to create the `agda` directory by myself).

### Installation methods

On Windows, **before doing anything**,
issue a `CHCP 65001` command on the cmd you are working on.
Otherwise, agda2hs won't be able to write Unicode characters
into .hs files.
If you have already run it without the command and it has failed,
_delete the generated Haskell files_ and only then try again.

For making this changes permanent, see [this tutorial](https://www.scaledeskit.net/post/How-to-set-default-charset-in-Windows-cmd).

#### Cabal (for use with Haskell packages)

Acorn is a full Cabal package.
When Cabal is run, the program in Setup.hs compiles the Agda sources
into the `hs` output directory;
the normal building process begins only then.

#### CMake (for use with C and C++ programs)

Ensure (especially on Windows) you have everything needed in your path:
- CMake itself;
- the generator (Make, Ninja or something similar);
- GHC;
- a C compiler.

For now, this has only been tested _on Ubuntu 20.04_.
But hopefully, I will make it work on Windows too.

For compiling a static library for use in C or C++,
use CMake:

```sh
cmake -G <your build system> CMakeLists.txt
```

On Unix, Make is the simplest option for the underlying build system;
on Windows, I use Ninja.
Run that build system after this.

You might be instructed to install libraries
("it is a member of the hidden package ...").
In this case, `cabal install --lib` will help
(although it's not too elegant).

The install command installs the library into a specific folder,
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
