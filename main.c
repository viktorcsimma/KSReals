#include <stdio.h>
#include "HsFFI.h"

void agdaMain();

// A primitive C main function
// which only calls a Haskell function
// and terminates.
int main(int argc, char* argv[]) {
  hs_init(&argc, &argv);
  agdaMain();
  hs_exit();
  return 0;
}
