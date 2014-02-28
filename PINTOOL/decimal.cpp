#include "TaintManager.h"
#include "decimal.h"
#include "buildFormula.h"

// CALLBACKS

void DECIMAL::cAAA(INS &ins)
{
    // AAA : ASCII Adjust After Addition
    // juste besoin de la valeur des flags (pour AF) et de AL
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAA,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        CALLBACK_DEBUG IARG_END);
} // cAAA

void DECIMAL::cAAD(INS &ins)
{
    // AAD : ASCII Adjust AX Before Division
    // besoin de la valeur d'AX et de la base de calcul (base 10 par defaut)
    UINT32 baseValue = static_cast<UINT32>(INS_OperandImmediate(ins, 0));

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAD,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AX,
        IARG_UINT32,    baseValue,
        CALLBACK_DEBUG IARG_END);
} // cAAD

void DECIMAL::cAAM(INS &ins)
{
    // AAM : ASCII Adjust AX After Multiply
    // juste besoin de la base de calcul (base 10 par defaut)
    UINT32 baseValue = static_cast<UINT32>(INS_OperandImmediate(ins, 0));

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAM,
        IARG_THREAD_ID,
        IARG_UINT32,    baseValue,
        CALLBACK_DEBUG IARG_END);
} // cAAM

void DECIMAL::cAAS(INS &ins)
{
    // AAS : ASCII Adjust AL After Substraction
    // besoin d'AX et des flags (pour AF)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAS,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AX,
        IARG_REG_VALUE, REG_GFLAGS,
        CALLBACK_DEBUG IARG_END);
} // cAAS

void DECIMAL::cDAA(INS &ins)
{
    // DAA : Decimal Adjust AL After Addition
    // besoin de la valeur d'AL et des flags (Carry et Aux)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sDAA,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        CALLBACK_DEBUG IARG_END);
} // cDAA

void DECIMAL::cDAS(INS &ins)
{
    // DAS : Decimal Adjust AL After Subbstraction
    // besoin de la valeur d'AL et des flags (Carry et Aux)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sDAS,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        CALLBACK_DEBUG IARG_END);
} // cDAS

// SIMULATE

void DECIMAL::sAAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue ADDRESS_DEBUG)
{
   /* SOURCE: BOCHS 2.6 (cpu\bcd.cc)
    *    IF (((AL and 0FH) > 9) or (AF==1)
    *    THEN
    *        AL <- AL+6 ; AH <- AH+1 ; CF <- 1 ; AF <- 1 ; AL <- AL and 0Fh 
    *    ELSE
    *        CF <- 0 ; AF <- 0 ; AL <- AL and 0Fh 
    *    ENDIF
    */

    // AAA agit comme un CMOV : il s'agit d'un branchement conditionnel "déguisé"
    // Il faut donc insérer une contrainte sur la valeur de "((AL and 0x0F) > 9) or (AF==1)" 
    // afin de pouvoir l'inverser 
    // puis selon la valeur de l'expression, AH et AL seront mis à jour ou non
    // EN REVANCHE CF et AF sont DEMARQUES (idem SETcc : leur valeur est fixe : 0 ou 1)
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);
    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isAFTainted     = pTmgrTls->isAuxiliaryFlagTainted();
    
    bool isALOver9       = ((regALValue & 0x0f) > 9) ? true : false ;
    bool isAFSet         = ((flagsValue >> AUXILIARY_FLAG) & 1) ? true : false;
    bool isTestTrue      = isALOver9 | isAFSet;
    

} // sAAA

void DECIMAL::sAAD(THREADID tid, ADDRINT regAXValue, ADDRINT immValue ADDRESS_DEBUG)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sAAD

void DECIMAL::sAAM(THREADID tid, ADDRINT immValue ADDRESS_DEBUG)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sAAM

void DECIMAL::sAAS(THREADID tid, ADDRINT regAXValue, ADDRINT flagsValue ADDRESS_DEBUG)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sAAS

void DECIMAL::sDAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue ADDRESS_DEBUG)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sDAA

void DECIMAL::sDAS(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue ADDRESS_DEBUG)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sDAS