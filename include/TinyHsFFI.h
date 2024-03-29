/* Copied from HsFFI.h;
   it only contains the things necessary for us. */

/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2000
 *
 * A mapping for Haskell types to C types, including the corresponding bounds.
 * Intended to be used in conjunction with the FFI.
 *
 * WARNING: Keep this file and StgTypes.h in synch!
 *
 * ---------------------------------------------------------------------------*/

/* N.B. Only use C-style multi-line comments in this file to avoid upsetting
 * dtrace on SmartOS, which doesn't support C++-style single-line comments.
 */

#pragma once

#if defined(__cplusplus)
extern "C" {
#endif

/* get types from GHC's runtime system */
/* we comment this out; we won't have these headers:D
#include "ghcconfig.h"
#include "stg/Types.h"
*/

/* for integer types */
#include <stdint.h>

/* get limits for floating point types */
#include <float.h>

/* now, these definitions are from Types.h */
/*
 * First, platform-dependent definitions of size-specific integers.
 */

typedef int8_t                   StgInt8;
typedef uint8_t                  StgWord8;

#define STG_INT8_MIN             INT8_MIN
#define STG_INT8_MAX             INT8_MAX
#define STG_WORD8_MAX            UINT8_MAX

#define FMT_Word8                PRIu8
#define FMT_HexWord8             PRIx8

typedef int16_t                  StgInt16;
typedef uint16_t                 StgWord16;

#define STG_INT16_MIN            INT16_MIN
#define STG_INT16_MAX            INT16_MAX
#define STG_WORD16_MAX           UINT16_MAX

#define FMT_Word16               PRIu16
#define FMT_HexWord16            PRIx16

typedef int32_t                  StgInt32;
typedef uint32_t                 StgWord32;

#define STG_INT32_MIN            INT32_MIN
#define STG_INT32_MAX            INT32_MAX
#define STG_WORD32_MAX           UINT32_MAX

#define FMT_Word32               PRIu32
#define FMT_HexWord32            PRIx32
#define FMT_Int32                PRId32

typedef int64_t                  StgInt64;
typedef uint64_t                 StgWord64;

#define STG_INT64_MIN            INT64_MIN
#define STG_INT64_MAX            INT64_MAX
#define STG_WORD64_MAX           UINT64_MAX

#define FMT_Word64               PRIu64
#define FMT_HexWord64            PRIx64
#define FMT_Int64                PRId64

typedef struct { StgWord64 h; StgWord64 l; } StgWord128;

typedef struct { StgWord128 h; StgWord128 l; } StgWord256;

typedef struct { StgWord256 h; StgWord256 l; } StgWord512;

/*
 * Stg{Int,Word} are defined such that they have the exact same size as a
 * void pointer.
 */

/* A clever solution to determine size of pointer type
   from https://stackoverflow.com/questions/51616057/how-to-determine-pointer-size-preprocessor-c. */

#if UINTPTR_MAX == 0xFFFF
  #define SIZEOF_VOID_P 2
#elif UINTPTR_MAX == 0xFFFFFFFF
  #define SIZEOF_VOID_P 4
#elif UINTPTR_MAX == 0xFFFFFFFFFFFFFFFFu
  #define SIZEOF_VOID_P 8
#else
  #error TBD pointer size
#endif

#if SIZEOF_VOID_P == 8
typedef int64_t            StgInt;
typedef uint64_t           StgWord;

typedef int32_t            StgHalfInt;
typedef uint32_t           StgHalfWord;

#define STG_INT_MIN        INT64_MIN
#define STG_INT_MAX        INT64_MAX
#define STG_WORD_MAX       UINT64_MAX

#define FMT_Word           FMT_Word64
#define FMT_HexWord        FMT_HexWord64
#define FMT_Int            FMT_Int64

#define strToStgWord       strtoull

#elif SIZEOF_VOID_P == 4
typedef int32_t            StgInt;
typedef uint32_t           StgWord;

typedef int16_t            StgHalfInt;
typedef uint16_t           StgHalfWord;

#define STG_INT_MIN        INT32_MIN
#define STG_INT_MAX        INT32_MAX
#define STG_WORD_MAX       UINT32_MAX

#define FMT_Word           FMT_Word32
#define FMT_HexWord        FMT_HexWord32
#define FMT_Int            FMT_Int32

#define strToStgWord       strtoul

#else
#error GHC untested on this architecture: sizeof(void *) != 4 or 8
#endif

#define W_MASK  (sizeof(W_)-1)

/*
 * Other commonly-used STG datatypes.
 */

typedef void*              StgAddr;
typedef StgWord32          StgChar;
typedef int                StgBool;
typedef float              StgFloat;
typedef double             StgDouble;
typedef StgWord*           StgPtr;           /* heap or stack pointer */
typedef StgWord volatile*  StgVolatilePtr;   /* pointer to volatile word   */
typedef StgWord            StgOffset;        /* byte offset within closure */
typedef StgWord8           StgCode;          /* close enough */
typedef void*              StgStablePtr;
typedef StgWord8*          StgByteArray;

/* and now from HsFFI: */
typedef StgChar                 HsChar;
typedef StgInt                  HsInt;
typedef StgInt8                 HsInt8;
typedef StgInt16                HsInt16;
typedef StgInt32                HsInt32;
typedef StgInt64                HsInt64;
typedef StgWord                 HsWord;
typedef StgWord8                HsWord8;
typedef StgWord16               HsWord16;
typedef StgWord32               HsWord32;
typedef StgWord64               HsWord64;
typedef StgFloat                HsFloat;
typedef StgDouble               HsDouble;
typedef StgInt                  HsBool;
typedef void*                   HsPtr;          /* this should better match StgAddr */
typedef void                    (*HsFunPtr)(void); /* this should better match StgAddr */
typedef void*                   HsStablePtr;

/* this should correspond to the type of StgChar in StgTypes.h */
#define HS_CHAR_MIN             0
#define HS_CHAR_MAX             0x10FFFF

/* is it true or not?  */
#define HS_BOOL_FALSE           0
#define HS_BOOL_TRUE            1

#define HS_BOOL_MIN             HS_BOOL_FALSE
#define HS_BOOL_MAX             HS_BOOL_TRUE


#define HS_INT_MIN              STG_INT_MIN
#define HS_INT_MAX              STG_INT_MAX
#define HS_WORD_MAX             STG_WORD_MAX

#define HS_INT8_MIN             STG_INT8_MIN
#define HS_INT8_MAX             STG_INT8_MAX
#define HS_INT16_MIN            STG_INT16_MIN
#define HS_INT16_MAX            STG_INT16_MAX
#define HS_INT32_MIN            STG_INT32_MIN
#define HS_INT32_MAX            STG_INT32_MAX
#define HS_INT64_MIN            STG_INT64_MIN
#define HS_INT64_MAX            STG_INT64_MAX
#define HS_WORD8_MAX            STG_WORD8_MAX
#define HS_WORD16_MAX           STG_WORD16_MAX
#define HS_WORD32_MAX           STG_WORD32_MAX
#define HS_WORD64_MAX           STG_WORD64_MAX

#define HS_FLOAT_RADIX          FLT_RADIX
#define HS_FLOAT_ROUNDS         FLT_ROUNDS
#define HS_FLOAT_EPSILON        FLT_EPSILON
#define HS_FLOAT_DIG            FLT_DIG
#define HS_FLOAT_MANT_DIG       FLT_MANT_DIG
#define HS_FLOAT_MIN            FLT_MIN
#define HS_FLOAT_MIN_EXP        FLT_MIN_EXP
#define HS_FLOAT_MIN_10_EXP     FLT_MIN_10_EXP
#define HS_FLOAT_MAX            FLT_MAX
#define HS_FLOAT_MAX_EXP        FLT_MAX_EXP
#define HS_FLOAT_MAX_10_EXP     FLT_MAX_10_EXP

#define HS_DOUBLE_RADIX         DBL_RADIX
#define HS_DOUBLE_ROUNDS        DBL_ROUNDS
#define HS_DOUBLE_EPSILON       DBL_EPSILON
#define HS_DOUBLE_DIG           DBL_DIG
#define HS_DOUBLE_MANT_DIG      DBL_MANT_DIG
#define HS_DOUBLE_MIN           DBL_MIN
#define HS_DOUBLE_MIN_EXP       DBL_MIN_EXP
#define HS_DOUBLE_MIN_10_EXP    DBL_MIN_10_EXP
#define HS_DOUBLE_MAX           DBL_MAX
#define HS_DOUBLE_MAX_EXP       DBL_MAX_EXP
#define HS_DOUBLE_MAX_10_EXP    DBL_MAX_10_EXP

extern void hs_init     (int *argc, char **argv[]);
extern void hs_exit     (void);
extern void hs_exit_nowait(void);
extern void hs_set_argv (int argc, char *argv[]);
extern void hs_thread_done (void);
extern void hs_restoreConsoleCP (void);

extern void hs_perform_gc (void);

/* Lock the stable pointer table. The table must be unlocked
 * again before calling any Haskell functions, even if those
 * functions do not manipulate stable pointers. The Haskell
 * garbage collector will not be able to run until this lock
 * is released! It is also forbidden to call hs_free_fun_ptr
 * or any stable pointer-related FFI functions other than
 * hs_free_stable_ptr_unsafe while the table is locked.
 */
extern void hs_lock_stable_ptr_table (void);

/* A deprecated synonym. */
extern void hs_lock_stable_tables (void);

/* Unlock the stable pointer table. */
extern void hs_unlock_stable_ptr_table (void);

/* A deprecated synonym. */
extern void hs_unlock_stable_tables (void);

/* Free a stable pointer assuming that the stable pointer
 * table is already locked.
 */
extern void hs_free_stable_ptr_unsafe (HsStablePtr sp);

extern void hs_free_stable_ptr (HsStablePtr sp);
extern void hs_free_fun_ptr    (HsFunPtr fp);

extern StgPtr hs_spt_lookup(StgWord64 key[2]);
extern int hs_spt_keys(StgPtr keys[], int szKeys);
extern int hs_spt_key_count (void);

extern void hs_try_putmvar (int capability, HsStablePtr sp);

/* -------------------------------------------------------------------------- */



#if defined(__cplusplus)
}
#endif
