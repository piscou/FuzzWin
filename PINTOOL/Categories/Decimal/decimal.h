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
void sAAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue ADDRESS_DEBUG);
void sAAD(THREADID tid, ADDRINT regAXValue, ADDRINT immValue ADDRESS_DEBUG);
void sAAM(THREADID tid, ADDRINT immValue ADDRESS_DEBUG);
void sAAS(THREADID tid, ADDRINT regAXValue, ADDRINT flagsValue ADDRESS_DEBUG);

void sDAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue ADDRESS_DEBUG);
void sDAS(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue ADDRESS_DEBUG);
}