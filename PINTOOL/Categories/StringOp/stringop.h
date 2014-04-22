#pragma once
#include <TaintEngine\TaintManager.h>

namespace STRINGOP 
{
// CALLBACKS 
void cCMPS(INS &ins, UINT32 size);  
void cLODS(INS &ins, UINT32 size);
void cMOVS(INS &ins, UINT32 size);  
void cSCAS(INS &ins, UINT32 size);  
void cSTOS(INS &ins, UINT32 size);  

// SIMULATE 
ADDRINT PIN_FAST_ANALYSIS_CALL returnArg (BOOL arg);

template<UINT32 lengthInBits> 
void sMOVS(ADDRINT count, ADDRINT flagsValue, ADDRINT readAddress, ADDRINT writeAddress, ADDRINT insAddress);

template<UINT32 lengthInBits> 
void sLODS(THREADID tid, ADDRINT count, ADDRINT flagsValue, ADDRINT readAddress, ADDRINT insAddress);

template<UINT32 lengthInBits> 
void sSTOS(THREADID tid, ADDRINT count, ADDRINT flagsValue, ADDRINT writeAddress, ADDRINT insAddress);

template<UINT32 lengthInBits> 
void sSCAS(THREADID tid, ADDRINT address);
template<UINT32 lengthInBits> 
void sStoreTaintSCAS(THREADID tid, BOOL isREPZ, ADDRINT regValue, ADDRINT insAddress);

template<UINT32 lengthInBits> 
void sCMPS(THREADID tid, UINT32 repCode, ADDRINT esiAddr, ADDRINT ediAddr, ADDRINT insAddress);

} // namespace STRINGOP

#include "stringop.hpp"
