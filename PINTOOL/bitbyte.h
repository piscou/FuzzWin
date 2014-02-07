#pragma once
#include "pintool.h"

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
void sSETB_M  (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETNB_M (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETS_M  (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETNS_M (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETO_M  (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETNO_M (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETP_M  (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETNP_M (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETZ_M  (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETNZ_M (THREADID tid, ADDRINT address, ADDRINT insAddress);
void sSETBE_M (THREADID tid, ADDRINT address, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETNBE_M(THREADID tid, ADDRINT address, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETL_M  (THREADID tid, ADDRINT address, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETNL_M (THREADID tid, ADDRINT address, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETLE_M (THREADID tid, ADDRINT address, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETNLE_M(THREADID tid, ADDRINT address, ADDRINT eflagsValue, ADDRINT insAddress);
// destination registre
void sSETB_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETNB_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETS_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETNS_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETO_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETNO_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETP_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETNP_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETZ_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETNZ_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress);
void sSETBE_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETNBE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETL_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETNL_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETLE_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress);
void sSETNLE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress);
 


// SIMULATE
// Simulate : bits tests
template<UINT32 len> void sBT_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 len> void sBT_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 len> void sBT_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 len> void sBT_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 

template<UINT32 len> void sBTC_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 len> void sBTC_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 len> void sBTC_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 len> void sBTC_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 

template<UINT32 len> void sBTR_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 len> void sBTR_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 len> void sBTR_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 len> void sBTR_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG);  

template<UINT32 len> void sBTS_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG); 
template<UINT32 len> void sBTS_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG);
template<UINT32 len> void sBTS_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG); 
template<UINT32 len> void sBTS_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG);  

template<UINT32 len> void sBSR_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG); 
template<UINT32 len> void sBSR_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG resultReg ADDRESS_DEBUG); 

template<UINT32 len> void sBSF_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG); 
template<UINT32 len> void sBSF_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG resultReg ADDRESS_DEBUG); 
} // namespace BITBYTE


#include "bitbyte.hpp"