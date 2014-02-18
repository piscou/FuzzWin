#pragma once
#include "pintool.h"
#include "binary.h" // CMP (pour CMPXCHG)
#include "dataxfer.h" // MOV (pour CMPXCHG)

namespace SEMAPHORE
{
// Callbacks
void cCMPXCHG(INS &ins);
void cCMPXCHG8B(INS &ins);
void cXADD(INS &ins);

#if TARGET_IA32E
void cCMPXCHG16B(INS &ins);
#endif

// simulate
template<UINT32 lengthInBits> 
void sCMPXCHG_RM(THREADID tid, REG regSrc, ADDRINT address, REG cmpReg, ADDRINT cmpRegValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sCMPXCHG_RR(THREADID tid, REG regSrc, REG regDest, ADDRINT regDestValue, REG cmpReg, ADDRINT cmpRegValue ADDRESS_DEBUG);

void sCMPXCHG8B(THREADID tid, ADDRINT address, ADDRINT regEAXValue, ADDRINT regEDXValue ADDRESS_DEBUG);

#if TARGET_IA32E
void sCMPXCHG16B(THREADID tid, ADDRINT address, ADDRINT regRAXValue, ADDRINT regRDXValue ADDRESS_DEBUG);
#endif

} // namespace SEMAPHORE

#include "semaphore.hpp"
