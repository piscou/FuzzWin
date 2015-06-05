#pragma once
#include <TaintEngine\TaintManager.h>
#include <Translate\translateIR.h> // pour SALC

namespace FLAGOP
{
    // CALLBACKS
    void cCLC_STC(INS &ins);
    void cCMC(INS &ins);

    void cLAHF(INS &ins);
    void cSAHF(INS &ins);

    void cSALC(INS &ins);

    // SIMULATE
    void sCLC_STC(THREADID tid, ADDRINT insAddress);
    void sCMC(THREADID tid, ADDRINT insAddress);

    void sLAHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT insAddress);
    void sSAHF(THREADID tid, ADDRINT insAddress);

    void sSALC(THREADID tid, ADDRINT regFlagsValue, ADDRINT insAddress);
} // namespace FLAGOP