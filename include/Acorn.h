#include "TinyHsFFI.h"
#if defined(__cplusplus)
extern "C" {
#endif

// from the FFI
extern HsStablePtr initCalcDyadic(void);
extern HsStablePtr initCalcRational(void);
extern HsPtr execCommandDyadic(HsStablePtr a1, HsPtr a2, HsInt32 a3);
extern HsPtr execCommandRational(HsStablePtr a1, HsPtr a2, HsInt32 a3);
extern HsPtr reevalCommandDyadic(HsStablePtr a1, HsInt32 a2);
extern HsPtr reevalCommandRational(HsStablePtr a1, HsInt32 a2);
extern void destructCalcDyadic(HsStablePtr a1);
extern void destructCalcRational(HsStablePtr a1);

// This is written by ourselves in src/acornInterruptEvaluation.c.
// It interrupts a running calculation
// by opening and incrementing the "/AcornInterruptSemaphore" POSIX semaphore (on Unix)
// or opening and triggering the "AcornInterruptEvent" event (on Windows).
extern void acornInterruptEvaluation();

#if defined(__cplusplus)
}
#endif

