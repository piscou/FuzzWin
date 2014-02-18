#pragma once
#include "TaintManager.h"

#include "DATAXFER.h" // pour LEAVE (POP encodé en MOVMR)
#include "utils.h" // pour computeEA

namespace MISC 
{
// CALLBACKS 
void cLEA(INS &ins);
void cLEAVE(INS &ins);

// SIMULATE 
template<UINT32 lengthInBitsEA, UINT32 lengthInBitsDest> void sLEA_BD
    (THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, INT32 displ ADDRESS_DEBUG);

template<UINT32 lengthInBitsEA, UINT32 lengthInBitsDest> void sLEA_ISD
    (THREADID tid, REG regDest, REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ ADDRESS_DEBUG);

template<UINT32 lengthInBitsEA, UINT32 lengthInBitsDest> void sLEA_BISD
    (THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, REG indexReg, ADDRINT indexRegValue, 
    UINT32 scale, INT32 displ ADDRESS_DEBUG);

// marquage de la destination, dépendant des longueurs source et destination
#if TARGET_IA32
void taintLEA(TaintManager_Thread *pTmgrTls, REG regDest, UINT32 lengthInBitsEA, UINT32 lengthInBitsDest, const TaintDwordPtr &tPtr);
#else
void taintLEA(TaintManager_Thread *pTmgrTls, REG regDest, UINT32 lengthInBitsEA, UINT32 lengthInBitsDest, const TaintQwordPtr &tPtr);
#endif
} // namespace MISC

#include "misc.hpp"
