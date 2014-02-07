#pragma once
#include "pintool.h" 

namespace CMOV
{
// CALLBACKS
void cCMOVB  (INS &ins);
void cCMOVNB (INS &ins);
void cCMOVS  (INS &ins);
void cCMOVNS (INS &ins);
void cCMOVO  (INS &ins);
void cCMOVNO (INS &ins);
void cCMOVP  (INS &ins);
void cCMOVNP (INS &ins);
void cCMOVZ  (INS &ins);
void cCMOVNZ (INS &ins);
void cCMOVBE (INS &ins);
void cCMOVNBE(INS &ins);
void cCMOVL  (INS &ins);
void cCMOVNL (INS &ins);
void cCMOVLE (INS &ins);
void cCMOVNLE(INS &ins);

void cIfPredicated_CMOVcc(INS &ins);
  
// SIMULATE
void sCMOVB  (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVNB (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVS  (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVNS (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVO  (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVNO (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVP  (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVNP (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVZ  (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVNZ (THREADID tid, bool isTaken, ADDRINT insAddress);
void sCMOVBE (THREADID tid, bool isTaken, ADDRINT eflagsValue, ADDRINT insAddress);
void sCMOVNBE(THREADID tid, bool isTaken, ADDRINT eflagsValue, ADDRINT insAddress);
void sCMOVL  (THREADID tid, bool isTaken, ADDRINT eflagsValue, ADDRINT insAddress);
void sCMOVNL (THREADID tid, bool isTaken, ADDRINT eflagsValue, ADDRINT insAddress);
void sCMOVLE (THREADID tid, bool isTaken, ADDRINT eflagsValue, ADDRINT insAddress);
void sCMOVNLE(THREADID tid, bool isTaken, ADDRINT eflagsValue, ADDRINT insAddress);
} // namespace CMOV