#pragma once
#include "pintool.h"

namespace INSTRUMENTATION 
{
    void Instruction(INS ins, void *);
     
    void FiniTaint(INT32 code, void *);
    void FiniCheckScore(INT32 code, void *);

    void threadStart(THREADID tid, CONTEXT *ctxt, INT32 flags, void *);
    void threadFini (THREADID tid, const CONTEXT *ctxt, INT32 flags, void *);

    void changeCtx(THREADID tid, CONTEXT_CHANGE_REASON reason,
                        const CONTEXT *, CONTEXT *, INT32 sig, VOID *);
    void insCount(TRACE trace, VOID *);
}