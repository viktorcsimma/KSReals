# the options passed to the C compiler
CFLAGS= -c -Wall -Wextra

all: a.out

a.out: hsobjects main.o
	ghc -no-hs-main `find . -type f -iname "*.o" -print`

main.o:
	ghc -no-hs-main $(CFLAGS) main.c

hsobjects: hssource
	ghc AgdaMain.hs

hssource:
	agda2hs AgdaMain.agda

clean:
	rm -rf `find . -type f -iname "*.o" "*.hs" -print`
