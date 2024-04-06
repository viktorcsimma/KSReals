#include "../include/Acorn.h"
#include <stdio.h>

#ifdef _WIN32
#include <windows.h>
#else
#if defined(__unix__) || defined(__unix) || \
        (defined(__APPLE__) && defined(__MACH__))
#include <unistd.h>
#endif
#endif

// See Acorn.h for description.
#ifdef _WIN32
void acornInterruptEvaluation() {
  // here, we won't actually use the handle
  HANDLE eventHandle = OpenEventA(
    EVENT_MODIFY_STATE,
    FALSE,
    "AcornInterruptEvent"
  );
  BOOL success = SetEvent(eventHandle);
  CloseHandle(eventHandle);
  if (! success ) {
    CloseHandle(eventHandle);
    fprintf(stderr, "SetEvent failed (%lu)\n", GetLastError());
    exit(1);
  }
}
#else
#if defined(__unix__) || defined(__unix) || \
        (defined(__APPLE__) && defined(__MACH__))
void acornInterruptEvaluation() {
  fprintf(stderr, "interruptCalculation not yet implemented on Unix\n");
  exit(1);
}
#endif
#endif
