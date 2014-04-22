#pragma once
#include <TaintEngine\TaintManager.h>

namespace UNCONDITIONAL_BR 
{
// CALLBACKS 
void cJMP(INS &ins);

// SIMULATE 
void sJMP_R(THREADID tid, REG reg, ADDRINT regValue, ADDRINT insAddress);

#if TARGET_IA32
// x86 : Effective Address vaut 16 ou 32 bits
void sJMP_BD_16(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, INT32 displ, ADDRINT insAddress);
void sJMP_ISD_16(THREADID tid, ADDRINT ea, REG indexReg, ADDRINT indexRegValue, 
                 UINT32 scale, INT32 displ, ADDRINT insAddress);
void sJMP_BISD_16(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, 
                  REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ, ADDRINT insAddress);

void sJMP_BD_32(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, INT32 displ, ADDRINT insAddress);
void sJMP_ISD_32(THREADID tid, ADDRINT ea, REG indexReg, ADDRINT indexRegValue, 
                 UINT32 scale, INT32 displ, ADDRINT insAddress);
void sJMP_BISD_32(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, 
                  REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ, ADDRINT insAddress);

#else
// x64 : Effective Address vaut 64 bits uniquement
void sJMP_BD_64(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, INT32 displ, ADDRINT insAddress);
void sJMP_ISD_64(THREADID tid, ADDRINT ea, REG indexReg, ADDRINT indexRegValue, 
                 UINT32 scale, INT32 displ, ADDRINT insAddress);
void sJMP_BISD_64(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, 
                  REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ, ADDRINT insAddress);
#endif

} // namespace UNCONDITIONAL_BR
