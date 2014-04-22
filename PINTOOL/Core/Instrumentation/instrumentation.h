#pragma once
#include <TaintEngine\TaintManager.h>

namespace INSTRUMENTATION 
{
    void Instruction(INS ins, void *);
     
    void FiniTaint(INT32 code, void *);
    void FiniCheckScore(INT32 code, void *);

    void threadStart(THREADID tid, CONTEXT *, INT32 , void *);
    void threadFini (THREADID tid, const CONTEXT *, INT32 , void *);

    void changeCtx(THREADID tid, CONTEXT_CHANGE_REASON reason,
                        const CONTEXT *, CONTEXT *, INT32 sig, VOID *);
    void insCount(TRACE trace, VOID *);

    void Image(IMG img, void *);
}