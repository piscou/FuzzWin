#pragma once
#include <TaintEngine\TaintManager.h>

namespace FLAGOP
{
    // CALLBACKS
    void cCLC_STC(INS &ins);
    void cCMC(INS &ins);

    void cLAHF(INS &ins);
    void cSAHF(INS &ins);

    void cSALC(INS &ins);

    // SIMULATE
    void PIN_FAST_ANALYSIS_CALL sCLC_STC(THREADID tid, ADDRINT insAddress);
    void PIN_FAST_ANALYSIS_CALL sCMC(THREADID tid, ADDRINT insAddress);

    void sLAHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT insAddress);
    void sSAHF(THREADID tid, ADDRINT insAddress);

    void sSALC(THREADID tid, ADDRINT regALValue, ADDRINT insAddress);
} // namespace FLAGOP