# The goal of this Makefile is to provide easy-to-use commands
# for running different parts of the compiling process
# (i.e. agda2hs, Haskell to object files,
# object files to single object file, object files to executable,
# cleaning).

# the options passed to the C compiler within GHC
CFLAGS= -c -Wall -Wextra

all: AcornShell

AcornShell: Main.o
	# this recognises that the object files are already there
	ghc --make Main.hs -o AcornShell

# a single large object file to be used in C++
Acorn.o: Main.o
	# we exclude Main.o itself,
	# so that the main function does not confuse C++
	ld -relocatable `find . -type f -iname "*.o" -not -path 'Main.o' -print` -o Acorn.o

# compiling Haskell files to object files:
Main.o: Main.hs
	# TODO: this assumes Main.hs has everything we need as its dependency
	ghc -c --make Main.hs

# compiling Agda files to Haskell files:
Main.hs:
	agda2hs Main.agda

hssource:
	agda2hs AgdaMain.agda

# clean everything besides the Agda files themselves
clean:
	if test -f AcornShell; then rm -f AcornShell; fi
	rm -rf `find . -type f -iname "*.hi" -print`
	rm -rf `find . -type f -iname "*.o" -print`
	rm -rf `find . -type f -iname "*.hs" -print`

clean-hsobjects:
	if test -f AcornShell; then rm -f AcornShell; fi
	rm -rf `find . -type f -iname "*.hi" -print`
	rm -rf `find . -type f -iname "*.o" -print`
