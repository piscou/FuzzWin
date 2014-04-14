#pragma once
#include <TaintEngine\TaintManager.h>

namespace BITBYTE
{
// CALLBACKS
// Callbacks : bits tests
void cBT(INS &ins); 
void cBTC(INS &ins);
void cBTR(INS &ins);
void cBTS(INS &ins);
void cBSR(INS &ins);
void cBSF(INS &ins);

// Callbacks : SETcc
void cSETB  (INS &ins);
void cSETNB (INS &ins);
void cSETS  (INS &ins);
void cSETNS (INS &ins);
void cSETO  (INS &ins);
void cSETNO (INS &ins);
void cSETP  (INS &ins);
void cSETNP (INS &ins);
void cSETZ  (INS &ins);
void cSETNZ (INS &ins);
void cSETBE (INS &ins);
void cSETNBE(INS &ins);
void cSETL  (INS &ins);
void cSETNL (INS &ins);
void cSETLE (INS &ins);
void cSETNLE(INS &ins);

// Simulate : SETcc
// destination mémoire 
void sSETB_M  (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETNB_M (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETS_M  (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETNS_M (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETO_M  (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETNO_M (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETP_M  (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETNP_M (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETZ_M  (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETNZ_M (THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG);
void sSETBE_M (THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETNBE_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETL_M  (THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETNL_M (THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETLE_M (THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETNLE_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG);

// destination registre
void sSETB_R  (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETNB_R (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETS_R  (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETNS_R (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETO_R  (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETNO_R (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETP_R  (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETNP_R (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETZ_R  (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETNZ_R (THREADID tid, REG regDest ADDRESS_DEBUG);
void sSETBE_R (THREADID tid, REG regDest, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETNBE_R(THREADID tid, REG regDest, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETL_R  (THREADID tid, REG regDest, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETNL_R (THREADID tid, REG regDest, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETLE_R (THREADID tid, REG regDest, ADDRINT flagsValue ADDRESS_DEBUG);
void sSETNLE_R(THREADID tid, REG regDest, ADDRINT flagsValue ADDRESS_DEBUG);
 
// SIMULATE
// Simulate : bits tests
template<UINT32 lengthInBits> void sBT_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBT_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 lengthInBits> void sBT_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBT_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 

template<UINT32 lengthInBits> void sBTC_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBTC_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 lengthInBits> void sBTC_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBTC_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 

template<UINT32 lengthInBits> void sBTR_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBTR_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 lengthInBits> void sBTR_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBTR_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG);  

template<UINT32 lengthInBits> void sBTS_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBTS_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 lengthInBits> void sBTS_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBTS_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG);  

template<UINT32 lengthInBits> void sBSR_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBSR_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG resultReg ADDRESS_DEBUG); 

template<UINT32 lengthInBits> void sBSF_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG); 
template<UINT32 lengthInBits> void sBSF_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG resultReg ADDRESS_DEBUG); 
} // namespace BITBYTE

#include "bitbyte.hpp"