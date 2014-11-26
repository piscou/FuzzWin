#pragma once
#include <TaintEngine\TaintManager.h>

namespace ROTATE 
{
// CALLBACKS 
void cROL(INS &ins);
void cROR(INS &ins);
void cRCL(INS &ins);
void cRCR(INS &ins);

// SIMULATE 
template<UINT32 lengthInBits> 
void sROL_IM(THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT insAddress);        
template<UINT32 lengthInBits> 
void sROL_IR(THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sROL_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sROL_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT insAddress);
        
template<UINT32 lengthInBits> 
void sROR_IM(THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT insAddress);        
template<UINT32 lengthInBits> 
void sROR_IR(THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sROR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sROR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT insAddress);

template<UINT32 lengthInBits> 
void sRCL_IM(THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress);        
template<UINT32 lengthInBits> 
void sRCL_IR(THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT regGflagsValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sRCL_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sRCL_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT regGflagsValue, ADDRINT insAddress);
     
template<UINT32 lengthInBits> 
void sRCR_IM(THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress);        
template<UINT32 lengthInBits> 
void sRCR_IR(THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT regGflagsValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sRCR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress);
template<UINT32 lengthInBits> 
void sRCR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT regGflagsValue, ADDRINT insAddress);
} // namespace ROTATE

#include "rotate.hpp"