#pragma once
#include "TaintManager.h"

namespace DATAXFER 
{
// CALLBACKS
void cMOV(INS &ins);
void cMOVZX(INS &ins);
void cMOVSX(INS &ins);
#if TARGET_IA32E
void cMOVSXD(INS &ins);
#endif
void cXCHG (INS &ins);
void cBSWAP(INS &ins);

// SIMULATE 
template<UINT32 len> void sMOV_RR(THREADID tid, REG regSrc, REG regDest ADDRESS_DEBUG);
template<> void sMOV_RR<8>(THREADID tid, REG regSrc, REG regDest ADDRESS_DEBUG);

template<UINT32 len> void sMOV_RM(THREADID tid, REG regSrc, ADDRINT writeAddress ADDRESS_DEBUG);
template<> void sMOV_RM<8>(THREADID tid, REG regSrc, ADDRINT writeAddress ADDRESS_DEBUG);

template<UINT32 len> void sMOV_MR(THREADID tid, ADDRINT readAddress, REG regDest ADDRESS_DEBUG);
template<> void sMOV_MR<8>(THREADID tid, ADDRINT readAddress, REG regDest ADDRESS_DEBUG);

template<UINT32 len> void sXCHG_M(THREADID tid, REG reg, ADDRINT address ADDRESS_DEBUG);
template<> void sXCHG_M<8>(THREADID tid, REG reg, ADDRINT address ADDRESS_DEBUG);
template<UINT32 len> void sXCHG_R(THREADID tid, REG regSrc, REG regDest ADDRESS_DEBUG);
template<> void sXCHG_R<8>(THREADID tid, REG regSrc, REG regDest ADDRESS_DEBUG);

template<UINT32 lenSrc, UINT32 lenDest> void sMOVSX_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, 
                                                       REG regDest ADDRESS_DEBUG);
template<UINT32 lenSrc, UINT32 lenDest> void sMOVSX_MR(THREADID tid, ADDRINT readAddress,
                                                       REG regDest ADDRESS_DEBUG);

template<UINT32 lenSrc, UINT32 lenDest> void sMOVZX_RR(THREADID tid, REG regSrc, REG regDest ADDRESS_DEBUG);
template<UINT32 lenDest> void sMOVZX_8R(THREADID tid, REG regSrc, REG regDest ADDRESS_DEBUG);
template<UINT32 lenSrc, UINT32 lenDest> void sMOVZX_MR(THREADID tid, ADDRINT readAddress, REG regDest ADDRESS_DEBUG);

template<UINT32 len> void sBSWAP(THREADID tid, REG reg ADDRESS_DEBUG); 
} // namespace DATAXFER

// définition des templates (hors templates spécialisés définis dans DATAXFER.cpp)
#include "DATAXFER.hpp"