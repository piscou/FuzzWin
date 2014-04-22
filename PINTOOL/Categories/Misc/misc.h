#pragma once
#include <TaintEngine\TaintManager.h>
#include <TaintUtilities\utils.h>   // pour computeEA
#include <Dataxfer\dataxfer.h>      // pour LEAVE (POP encodé en MOVMR)


namespace MISC 
{
// CALLBACKS 
void cLEA  (INS &ins);
void cLEAVE(INS &ins);
void cXLAT (INS &ins);
void cCPUID(INS &ins);

// SIMULATE 
template< UINT32 lenDest, UINT32 lenEA> 
void sLEA(THREADID tid, REG regDest, ADDRINT insAddress);

void PIN_FAST_ANALYSIS_CALL sCPUID(THREADID tid, ADDRINT insAddress);

} // namespace MISC

#include "misc.hpp"
