#pragma once
#include "TaintManager.h"

namespace LOGICAL 
{
// CALLBACKS 
void cAND(INS &ins);
void cOR(INS &ins);
void cXOR(INS &ins);
void cTEST(INS &ins);
void cNOT(INS &ins);

// FLAGS 
// marquage identique pour toutes les opérations LOGICAL, basé sur le résultat
void fTaintLOGICAL(TaintManager_Thread *pTmgr, const TaintPtr &resultPtr);

// SIMULATE 
template<UINT32 lengthInBits> 
void sAND_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sAND_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sAND_RM(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sAND_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sAND_RR(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);

template<> 
void sAND_IM<8>(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<> 
void sAND_IR<8>(THREADID tid, ADDRINT value, REG reg, ADDRINT unUsed ADDRESS_DEBUG);
template<> 
void sAND_RM<8>(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<> 
void sAND_MR<8>(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<> 
void sAND_RR<8>(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sOR_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sOR_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sOR_RM(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sOR_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sOR_RR(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);

template<> 
void sOR_IM<8>(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<> 
void sOR_IR<8>(THREADID tid, ADDRINT value, REG reg, ADDRINT unUsed ADDRESS_DEBUG);
template<> 
void sOR_RM<8>(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<> 
void sOR_MR<8>(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<> 
void sOR_RR<8>(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sXOR_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sXOR_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sXOR_RM(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sXOR_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sXOR_RR(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void PIN_FAST_ANALYSIS_CALL sXOR_RR_EQUAL(THREADID tid, REG reg ADDRESS_DEBUG);

template<> 
void sXOR_IM<8>(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<> 
void sXOR_IR<8>(THREADID tid, ADDRINT value, REG reg, ADDRINT unUsed ADDRESS_DEBUG);
template<> 
void sXOR_RM<8>(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<> 
void sXOR_MR<8>(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<> 
void sXOR_RR<8>(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sTEST_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sTEST_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sTEST_RM(THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sTEST_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sTEST_RR(THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sTEST_RR_EQUAL(THREADID tid, REG regSrc, ADDRINT srcValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sNOT_M(ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sNOT_R(THREADID tid, REG reg ADDRESS_DEBUG);
template<> 
void sNOT_R<8>(THREADID tid, REG reg ADDRESS_DEBUG);
} // namespace LOGICAL

#include "LOGICAL.hpp"