#pragma once
#include <TaintEngine\TaintManager.h>
#include <TaintUtilities\utils.h>
#include <Translate\translateIR.h> // ajout des contraintes sur les adresses de saut

namespace UNCONDITIONAL_BR 
{
// CALLBACKS 
void cJMP(INS &ins);

// SIMULATE 
template<UINT32 lengthInBits>
void sJMP_M(THREADID tid, ADDRINT effectiveAddress, ADDRINT jumpAddress, ADDRINT insAddress);

template<UINT32 lengthInBits>
void sJMP_R(THREADID tid, REG reg, ADDRINT jumpAddress, ADDRINT insAddress);
} // namespace UNCONDITIONAL_BR

#include "unconditional_branch.hpp"
