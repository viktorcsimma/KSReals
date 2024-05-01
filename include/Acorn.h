#ifndef ACORN_H_
#define ACORN_H_

#include "TinyHsFFI.h"
#if defined(__cplusplus)
extern "C" {
#endif

// from the FFI

// Initialises a CalcState with base type Dyadic
// and returns a StablePtr to it.
extern HsStablePtr initCalcDyadic(void);

// Initialises a CalcState with base type Rational
// and returns a StablePtr to it.
extern HsStablePtr initCalcRational(void);

// Executes a command with the current state of the CalcState object supplied
// and returns a pointer to the output in a C string.
// Remember that this has to be freed on the C side.
extern HsPtr execCommandDyadic(HsStablePtr calcState, HsPtr command, HsInt32 precision);

// Executes a command with the current state of the CalcState object supplied
// and returns a pointer to the output in a C string.
// Remember that this has to be freed on the C side.
extern HsPtr execCommandRational(HsStablePtr calcState, HsPtr command, HsInt32 precision);

// Reevaluates the last result with the given precision
// and returns a pointer to the output in a C string.
// Remember that this has to be freed on the C side.
extern HsPtr reevalCommandDyadic(HsStablePtr calcState, HsInt32 precision);

// Reevaluates the last result with the given precision
// and returns a pointer to the output in a C string.
// Remember that this has to be freed on the C side.
extern HsPtr reevalCommandRational(HsStablePtr calcState, HsInt32 precision);

// Frees the StablePtr to the CalcState object,
// as this could not be done from the C side.
extern void destructCalcDyadic(HsStablePtr calcState);

// Frees the StablePtr to the CalcState object,
// as this could not be done from the C side.
extern void destructCalcRational(HsStablePtr calcState);

// This is written by ourselves in src/acornInterruptEvaluation.c.
// It interrupts a running calculation
// by opening and incrementing the "/AcornInterruptSemaphore" POSIX semaphore (on Unix)
// or opening and triggering the "AcornInterruptEvent" event (on Windows).
extern void acornInterruptEvaluation();

#if defined(__cplusplus)
}
#endif

#endif
