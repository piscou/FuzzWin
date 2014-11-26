#pragma once
#include <TaintEngine\TaintManager.h>

namespace INSTRUMENTATION 
{
    void Instruction(INS ins, void *);
     
    void FiniTaint(INT32 code, void *);
    void FiniCheckScore(INT32 code, void *);

    void threadStart          (THREADID tid, CONTEXT *, INT32 , VOID *);
    void threadFini           (THREADID tid, const CONTEXT *, INT32 , VOID *);
    void ThreadStartCheckScore(THREADID tid, CONTEXT *, INT32 , VOID *);

    void changeCtx(THREADID tid, CONTEXT_CHANGE_REASON reason,
                        const CONTEXT *, CONTEXT *, INT32 sig, VOID *);
    void traceCheckScore(TRACE trace, VOID *);
    // fonction d'analyse qui compte le nombre d'instruction de chaque BBL
    void PIN_FAST_ANALYSIS_CALL docount(THREADID tid, ADDRINT bblCount);

    void Image(IMG img, void *);
}