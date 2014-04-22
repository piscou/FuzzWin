#pragma once
#include <TaintEngine\TaintManager.h>

namespace DECIMAL
{
// CALLBACKS
void cAAA(INS &ins);
void cAAD(INS &ins);
void cAAM(INS &ins);
void cAAS(INS &ins);
void cDAA(INS &ins);
void cDAS(INS &ins);

// SIMULATE
void sAAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress);
void sAAD(THREADID tid, ADDRINT regAXValue, ADDRINT immValue, ADDRINT insAddress);
void sAAM(THREADID tid, ADDRINT immValue, ADDRINT insAddress);
void sAAS(THREADID tid, ADDRINT regAXValue, ADDRINT flagsValue, ADDRINT insAddress);

void sDAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress);
void sDAS(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress);
}