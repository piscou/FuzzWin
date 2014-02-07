#pragma once
#include "pintool.h"

namespace INSTRUMENTATION 
{
    void Instruction(INS ins, void *);
    void Image(IMG img, void *);
    void Routine(RTN rtn, void *);

    ADDRINT PIN_FAST_ANALYSIS_CALL testMem(PIN_MEM_TRANS_INFO *memTransInfo, void *v);
    
    void Fini(INT32 code, void *);

    void threadStart(THREADID tid, CONTEXT *ctxt, INT32 flags, void *);
    void threadFini (THREADID tid, const CONTEXT *ctxt, INT32 flags, void *);
}