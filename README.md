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
On Ubuntu/Debian, it should suffice to say `sudo apt install zlib1g-dev libncurses5-dev`.

#### agda2hs

Of course, you will need agda2hs.
Acorn does **not** get compiled with the vanilla version;
_you need a modified one_.
It can be found on branch [`have-it-both-ways`](https://github.com/viktorcsimma/agda2hs/commit/a3c83ad3be876ce0c7aa31157f3107843bf2f465) on my fork.
(But hopefully, these changes will get merged soon.)
Clone it, check out the commit, then run `cabal install`.

If Cabal hangs on "Building Agda-2.x.x...", you can try pressing Control-C;
once, it proceeded with the installation then.

When done, add the Cabal binary path
(usually `~/.cabal/bin/` on Unix and `C:\cabal\bin\` on Windows)
to the PATH variable
so that the command interpreter sees and recognises agda2hs.

Lastly, in order to make Agda see the agda2hs standard library,
add the path to the `agda2hs.agda-lib` file in the project root
(e.g. `C:\path\to\agda2hs\agda2hs.agda-lib` on Windows)
to the global library list of Agda.
agda2hs will tell you where it is when you try to run it on `src/All.agda`
(on Windows, it was `AppData\Roaming\agda\libraries` for me;
but I had to create the `agda` directory and the file in it by myself).
It is important that the name is just `libraries`, without any extension –
some editors might try to add `.txt` after it.

### Installation methods

On Windows, **before doing anything**,
issue a `CHCP 65001` command on the cmd you are working on.
Otherwise, agda2hs will not be able to write Unicode characters
into .hs files.
If you have already run it without the command and it has failed,
delete the generated Haskell files and only then try again.

For changing the code page permanently,
see [this tutorial](https://www.scaledeskit.net/post/How-to-set-default-charset-in-Windows-cmd).

#### Cabal (for use with Haskell packages)

Acorn is a full Cabal package.
It can simply be built with `cabal build`
and installed with `cabal install`
(the latter also makes the AcornShell executable available
if you already have agda2hs in PATH).
For testing, enter `cabal test`;
that compiles and runs the QuickCheck test functions included.

#### CMake (for use with C and C++ programs)

Ensure (especially on Windows) you have everything needed in your PATH:
- CMake itself;
- the generator (Make, Ninja or something similar);
- GHC;
- a C compiler.

For compiling a static library for use in C or C++,
use CMake.
First, generate the scripts of the build system:

```sh
cmake -G <the_build_system_of_your_choice> CMakeLists.txt
```

Then, run your build system:
first build the library as a normal user,
then install it as a superuser.
I use Ninja on Windows
and Make on Linux.

After this is done,
two files will get created in the project root:
`libAcorn.a` and `AcornShell`/`AcornShell.exe`.

The install command installs the library into a specific folder,
where it is globally available for all CMake projects.
With some strings attached.

On Windows, for some reason,
`Interaction.o` gets corrupted and
the linker cannot see the symbols exported from `Interaction.agda`
(even though it does detect symbols of the Haskell runtime).
Therefore, you have to import `Interaction.o` separately.

Another caveat is that you need to pass some specific options to the linker
(see later),
in the `CMakeLists.txt` file of the project
from which you import the library.
GHC links the Haskell RTS runtimes into the library, so we need not worry about that;
however, for some reason ld does not find some system libraries by default.

Furthermore, it is essential that the C compiler you use for your client program
be of a similar version
as that used by your GHC installation.
On Linux, this did not pose any problems;
on Windows, however, I had to install an appropriate version of
[llvm-mingw](https://github.com/mstorsjo/llvm-mingw/releases)
(version 14.0.0 for GHC 9.4.8)
and compile everything with its Clang frontend.

[Here](https://github.com/viktorcsimma/acorn-calc/blob/main/CMakeLists.txt)
is an example CMakeLists.txt
for a test application `AcornCalc`
with source files `src/test.cpp` and `src/ViewModel/HsCalcStateWrapper.cpp`
and headers in the `include/` folder.
The relevant code for importing Acorn
(replace `calc` with the name of your executable):

```cmake
find_package(Acorn 0.1 REQUIRED)

# For some reason, on Windows, Interaction.o gets corrupted when copied into the library;
# so it has to be included separately.
target_link_libraries(calc PRIVATE Acorn::Acorn)
if("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
  target_link_libraries(calc PRIVATE "${CMAKE_INSTALL_PREFIX}/../Acorn/lib/Interaction.o")
endif()

# I am not sure why, but ld cannot detect some system libraries by itself;
# so they need to be named explicitly.
if("Linux" STREQUAL ${CMAKE_SYSTEM_NAME} OR "Darwin" STREQUAL ${CMAKE_SYSTEM_NAME})
  target_link_options(calc PRIVATE -no-pie)
  target_link_libraries(calc PRIVATE dl pthread gmp)
  if(CMAKE_BUILD_TYPE MATCHES RELEASE)
      # we tell the dynamic linker to search for shared libraries in the folder of the executable itself
      # this way, we can bundle the remaining libraries with the application
      target_link_options(calc PRIVATE -rpath=.)
  endif()
elseif("Windows" STREQUAL ${CMAKE_SYSTEM_NAME})
  target_link_options(calc PRIVATE -pthread -fno-PIC)
  target_link_libraries(calc PRIVATE ntdll rpcrt4 dbghelp ucrt msvcrt ws2_32 ucrt winmm)
else()
  message( FATAL_ERROR "Unsupported operating system: ${CMAKE_SYSTEM_NAME}" )
endif()
```

## Documentation

So far, a real documentation does not really exist.
The most detailed description about the library for now
is [this article](http://csimmaviktor.web.elte.hu/acorn.pdf).
But feel free to ask if you have questions.

## Contribution

Contributions are welcome!
