#pragma once
#include "TaintManager.h"

namespace SHIFT 
{
// CALLBACKS 
void cSHL(INS &ins);
void cSHR(INS &ins);
void cSAR(INS &ins);
void cSHLD(INS &ins);
void cSHRD(INS &ins);

// SIMULATE 
template<UINT32 lengthInBits> 
void sSHL_IM(THREADID tid, UINT32 maskedDepl, ADDRINT writeAddr ADDRESS_DEBUG);        
template<UINT32 lengthInBits> 
void sSHL_IR(THREADID tid, UINT32 maskedDepl, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHL_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHL_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue ADDRESS_DEBUG);
        
template<UINT32 lengthInBits> 
void sSHR_IM(THREADID tid, UINT32 maskedDepl, ADDRINT writeAddr ADDRESS_DEBUG);        
template<UINT32 lengthInBits> 
void sSHR_IR(THREADID tid, UINT32 maskedDepl, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue ADDRESS_DEBUG);

template<UINT32 lengthInBits> 
void sSAR_IM(THREADID tid, UINT32 maskedDepl, ADDRINT writeAddr ADDRESS_DEBUG);        
template<UINT32 lengthInBits> 
void sSAR_IR(THREADID tid, UINT32 maskedDepl, REG reg, ADDRINT regValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSAR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSAR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue ADDRESS_DEBUG);
        
template<UINT32 lengthInBits> 
void sSHLD_IM(THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddr ADDRESS_DEBUG);        
template<UINT32 lengthInBits> 
void sSHLD_IR(THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHLD_RM(THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHLD_RR(THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
 
template<UINT32 lengthInBits> 
void sSHRD_IM(THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddr ADDRESS_DEBUG);        
template<UINT32 lengthInBits> 
void sSHRD_IR(THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHRD_RM(THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG);
template<UINT32 lengthInBits> 
void sSHRD_RR(THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG);

//  FLAGS 
// marquage flags spécifique pour SHL, déplacement non marqué
void fSHL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl);
// marquage flags spécifique pour SHL, déplacement marqué
void fSHL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount);

// marquage flags spécifique pour SHR, déplacement non marqué
void fSHR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl);
// marquage flags spécifique pour SHR, déplacement marqué
void fSHR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount);

// marquage flags spécifique pour SAR, déplacement non marqué
void fSAR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl);
// marquage flags spécifique pour SAR, déplacement marqué
void fSAR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount);

// marquage flags spécifique pour SHLD, déplacement non marqué
void fSHLD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl);
// marquage flags spécifique pour SHLD, déplacement marqué
void fSHLD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount);

// marquage flags spécifique pour SHRD, déplacement non marqué
void fSHRD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objConcatenatedSrc,
          UINT32 maskedDepl);
// marquage flags spécifique pour SHRD, déplacement marqué
void fSHRD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objConcatenatedSrc,
          const ObjectSource &objTbCount);

// démarquage OZSAP
void fUnTaintOZSAP(TaintManager_Thread *pTmgrTls);
} // namespace SHIFT

#include "shift.hpp"
