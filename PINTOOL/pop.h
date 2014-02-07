#pragma once
#include "pintool.h" 

namespace POP 
{
// CALLBACKS        
void cPOP(INS &ins);
void cPOPF(INS &ins);
#if TARGET_IA32
void cPOPA(INS &ins);
void cPOPAD(INS &ins);
#endif
 
// SIMULATE 
template<UINT32 len> void sPOP_M(THREADID tid, ADDRINT writeAddress, ADDRINT stackAddressBeforePop ADDRESS_DEBUG);
template<UINT32 len> void sPOP_R(THREADID tid, REG regDest, ADDRINT stackAddressBeforePop ADDRESS_DEBUG);

#if TARGET_IA32
void sPOPA (THREADID tid, ADDRINT stackAddressBeforePop ADDRESS_DEBUG);
void sPOPAD(THREADID tid, ADDRINT stackAddressBeforePop ADDRESS_DEBUG);
#endif

void sPOPF(THREADID tid, ADDRINT stackAddressBeforePop ADDRESS_DEBUG);
} // namespace POP

#include "pop.hpp"
