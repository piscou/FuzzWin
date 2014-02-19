#pragma once
#include "TaintManager.h"

namespace BINARY 
{
// CALLBACKS 
void cNEG(INS &ins);
void cADC(INS &ins);
void cADD(INS &ins);
void cSBB(INS &ins);
void cSUB(INS &ins);
void cINC(INS &ins);
void cDEC(INS &ins);
void cCMP(INS &ins);
void cIMUL(INS &ins);
void cMUL(INS &ins);
void cDIVISION(INS &ins, bool isSignedDivision);

// FLAGS 
void fTaintNEG(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintPtr &resultPtr);
void fTaintINC(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintPtr &resultPtr);
void fTaintDEC(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintPtr &resultPtr);
void fTaintADD(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, 
                                              const ObjectSource &objSrc, const TaintPtr &resultPtr);
void fTaintSUB(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, 
                                              const ObjectSource &objSrc, const TaintPtr &resultPtr);
template<UINT32 lengthInBits> 
void fTaintCMP(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, const ObjectSource &objSrc);
void fTaintMUL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr);
void fTaintIMUL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr);
void fUnTaintINCDEC(TaintManager_Thread *pTmgrTls);

// SIMULATE 
template<UINT32 lengthInBits> 
void sNEG_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sNEG_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sINC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sINC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sDEC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sDEC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sADC_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue, ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADC_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADC_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue, 
                           ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADC_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress, 
                           ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADC_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, 
                           ADDRINT regSrcDestValue, ADDRINT flagsValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sADD_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADD_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADD_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADD_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sADD_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sSBB_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue, ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSBB_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSBB_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue, 
                           ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSBB_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress, 
                           ADDRINT flagsValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSBB_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, 
                           ADDRINT regSrcDestValue, ADDRINT flagsValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sSUB_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSUB_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSUB_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSUB_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSUB_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sCMP_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sCMP_IM(THREADID tid, ADDRINT value, ADDRINT readAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sCMP_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sCMP_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT readAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sCMP_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sIMUL_1M(THREADID tid, ADDRINT readAddress, ADDRINT implicitRegValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sIMUL_1R(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT implicitRegValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sIMUL_2MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sIMUL_2RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sIMUL_3M(THREADID tid, ADDRINT value, ADDRINT readAddress, REG regDest ADDRESS_DEBUG);
template<UINT32 lengthInBits>
void sIMUL_3R(THREADID tid, ADDRINT value, REG regSrc, ADDRINT regSrcValue, REG regDest ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sDIVISION_M(THREADID tid, ADDRINT readAddress, bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG);
        
template<UINT32 lengthInBits> 
void sDIVISION_R(THREADID tid, REG regSrc, ADDRINT regSrcValue, bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG);
} // namespace BINARY

// définition des templates
#include "BINARY.hpp"