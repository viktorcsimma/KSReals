#include <TinyHsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsStablePtr initCalcDyadic(void);
extern HsStablePtr initCalcRational(void);
extern HsPtr execCommandDyadic(HsStablePtr a1, HsPtr a2, HsInt32 a3);
extern HsPtr execCommandRational(HsStablePtr a1, HsPtr a2, HsInt32 a3);
extern HsPtr reevalCommandDyadic(HsStablePtr a1, HsInt32 a2);
extern HsPtr reevalCommandRational(HsStablePtr a1, HsInt32 a2);
extern void destructCalcDyadic(HsStablePtr a1);
extern void destructCalcRational(HsStablePtr a1);
#if defined(__cplusplus)
}
#endif

