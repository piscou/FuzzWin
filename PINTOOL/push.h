#pragma once
#include "pintool.h"

namespace PUSH 
{
void cPUSH(INS &ins);
void cPUSHA(INS &ins);
void cPUSHAD(INS &ins);
void cPUSHF(INS &ins);

// SIMULATE 
template<UINT32 len> void sPUSH_M(THREADID tid, ADDRINT readAddress, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
template<UINT32 len> void sPUSH_R(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
template<UINT32 len> void sPUSH_I(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);

#if TARGET_IA32
void sPUSHA(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
void sPUSHAD(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);
#endif
void sPUSHF(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG);

} // namespace PUSH

#include "push.hpp"
