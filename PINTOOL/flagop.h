#pragma once
#include "TaintManager.h"

namespace FLAGOP
{
    // CALLBACKS
    void cCLC_STC(INS &ins);
    void cCMC(INS &ins);

    void cLAHF(INS &ins);
    void cSAHF(INS &ins);

    void cSALC(INS &ins);

    // SIMULATE
    void PIN_FAST_ANALYSIS_CALL sCLC_STC(THREADID tid ADDRESS_DEBUG);
    void PIN_FAST_ANALYSIS_CALL sCMC(THREADID tid ADDRESS_DEBUG);

    void sLAHF(THREADID tid, ADDRINT regFlagsValue ADDRESS_DEBUG);
    void sSAHF(THREADID tid ADDRESS_DEBUG);

    void sSALC(THREADID tid, ADDRINT regALValue, ADDRINT insAddress);
} // namespace FLAGOP