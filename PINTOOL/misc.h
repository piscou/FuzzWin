#pragma once
#include "TaintManager.h"

#include "DATAXFER.h" // pour LEAVE (POP encodé en MOVMR)
#include "utils.h" // pour computeEA

namespace MISC 
{
// CALLBACKS 
void cLEA  (INS &ins);
void cLEAVE(INS &ins);
void cXLAT (INS &ins);
void cCPUID(INS &ins);

// SIMULATE 
template< UINT32 lenDest, UINT32 lenEA> void sLEA(THREADID tid, REG regDest ADDRESS_DEBUG);

template<UINT32 lengthInBitsEA, UINT32 lengthInBitsDest> 
void sLEA_BISD(THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, 
               REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ ADDRESS_DEBUG);

void PIN_FAST_ANALYSIS_CALL sCPUID(THREADID tid ADDRESS_DEBUG);

} // namespace MISC

#include "misc.hpp"
