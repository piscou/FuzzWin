#pragma once
#include <TaintEngine\TaintManager.h>

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
void sCMPXCHG_RM(THREADID tid, REG regSrc, ADDRINT address, REG cmpReg, ADDRINT cmpRegValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sCMPXCHG_RR(THREADID tid, REG regSrc, REG regDest, ADDRINT regDestValue, REG cmpReg, ADDRINT cmpRegValue, ADDRINT insAddress);

void sCMPXCHG8B(THREADID tid, ADDRINT address, ADDRINT regEAXValue, ADDRINT regEDXValue, ADDRINT insAddress);

#if TARGET_IA32E
void sCMPXCHG16B(THREADID tid, ADDRINT address, ADDRINT regRAXValue, ADDRINT regRDXValue, ADDRINT insAddress);
#endif

template<UINT32 lengthInBits>
void sXADD_R(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
template<UINT32 lengthInBits>
void sXADD_M(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress, ADDRINT insAddress);

} // namespace SEMAPHORE

#include "semaphore.hpp"
