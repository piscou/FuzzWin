#include "decimal.h"

// CALLBACKS

void DECIMAL::cAAA(INS &ins)
{
    // AAA : ASCII Adjust After Addition
    // juste besoin de la valeur des flags (pour AF) et de AL
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAA,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
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
        IARG_INST_PTR, IARG_END);
} // cAAD

void DECIMAL::cAAM(INS &ins)
{
    // AAM : ASCII Adjust AX After Multiply
    // juste besoin de la base de calcul (base 10 par defaut)
    UINT32 baseValue = static_cast<UINT32>(INS_OperandImmediate(ins, 0));

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAM,
        IARG_THREAD_ID,
        IARG_UINT32,    baseValue,
        IARG_INST_PTR, IARG_END);
} // cAAM

void DECIMAL::cAAS(INS &ins)
{
    // AAS : ASCII Adjust AL After Substraction
    // besoin d'AX et des flags (pour AF)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAS,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AX,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cAAS

void DECIMAL::cDAA(INS &ins)
{
    // DAA : Decimal Adjust AL After Addition
    // besoin de la valeur d'AL et des flags (Carry et Aux)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sDAA,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cDAA

void DECIMAL::cDAS(INS &ins)
{
    // DAS : Decimal Adjust AL After Subbstraction
    // besoin de la valeur d'AL et des flags (Carry et Aux)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sDAS,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cDAS

// SIMULATE

void DECIMAL::sAAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress)
{
   /* Manuel Intel:
    *    IF (((AL and 0FH) > 9) or (AF=1)
    *    THEN   AL <- AL+6 ; AH <- AH+1 ; CF <- 1 ; AF <- 1 ; AL <- AL and 0Fh 
    *    ELSE   CF <- 0 ; AF <- 0 ; AL <- AL and 0Fh   */
    
    // représentation des opérandes de destination par une relation pour chaque partie:
    // X_AAA_AL, X_AAA_AH, F_AAA (commun AF et CF)

    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isRegAHTainted  = pTmgrTls->isRegisterTainted<8>(REG_AH);
    bool isAFTainted     = pTmgrTls->isAuxiliaryFlagTainted();
    UINT32 AFValue       = EXTRACTBIT(flagsValue, AUXILIARY_FLAG);

    // condition du test non marquée
    if (!(isRegALTainted || isAFTainted))
    {
        // CF : démarquage (AL et AH le sont déjà)
        pTmgrTls->unTaintCarryFlag();

        // AH : s'il est marqué et que condition vraie, équivalent à un INC AH
        if (isRegAHTainted)
        {
            if (((regALValue & 0xf) > 9) || (AFValue == 1))
            {
                ObjectSource objAH(pTmgrTls->getRegisterTaint(REG_AH)); // forcément marqué
                pTmgrTls->updateTaintRegister<8>(REG_AH, std::make_shared<TaintByte>(X_INC, objAH));
            }
        }
    }
    else
    {


    }

} // sAAA

void DECIMAL::sAAD(THREADID tid, ADDRINT regAXValue, ADDRINT immValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sAAD

void DECIMAL::sAAM(THREADID tid, ADDRINT immValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sAAM

void DECIMAL::sAAS(THREADID tid, ADDRINT regAXValue, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sAAS

void DECIMAL::sDAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sDAA

void DECIMAL::sDAS(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

} // sDAS