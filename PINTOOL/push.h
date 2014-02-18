#pragma once
#include "pintool.h"
#include "TaintManager.h"

namespace PUSH 
{
// CALLBACKS
void cPUSH (INS &ins);
void cPUSHF(INS &ins, UINT32 size);

#if TARGET_IA32
void cPUSHA (INS &ins);
void cPUSHAD(INS &ins);
#endif

// SIMULATE 
template<UINT32 lengthInBits> 
void sUpdateEspTaint(TaintManager_Thread *pTmgrTls, ADDRINT stackAddressBeforePush);

template<UINT32 lengthInBits> 
void sPUSH_M(THREADID tid, ADDRINT readAddress, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sPUSH_R(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sPUSH_R_STACK(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sPUSH_I(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sPUSHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);

#if TARGET_IA32
void sPUSHA(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
void sPUSHAD(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
#endif
} // namespace PUSH

#include "push.hpp"
