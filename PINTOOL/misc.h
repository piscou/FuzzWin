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
template< UINT32 lenDest, UINT32 lenEA> void sLEA(THREADID tid, REG regDest ADDRESS_DEBUG);

} // namespace MISC

#include "misc.hpp"
