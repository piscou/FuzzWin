#pragma once
#include <TaintEngine\TaintManager.h> 
#include <TaintUtilities\utils.h>
#include <Translate\translateIR.h> // ajout des contraintes sur les adresses de saut

namespace CALL 
{
// CALLBACKS
void cCALL(INS &ins, bool isFarCall);

// SIMULATE 
template<UINT32 lengthInBits> 
void sCALL_M(THREADID tid, bool isFarCall, ADDRINT effectiveAddress, ADDRINT jumpAddress, ADDRINT stackValue, ADDRINT insAddress);

template<UINT32 lengthInBits> 
void sCALL_R(THREADID tid, bool isFarCall, REG reg, ADDRINT jumpAddress, ADDRINT stackValue, ADDRINT insAddress);
} // namespace CALL

#include "call.hpp"