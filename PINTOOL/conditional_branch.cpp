#include "conditional_branch.h"
#include "buildFormula.h"
#include "TaintManager.h"

void CONDITIONAL_BR::cJB(INS &ins) 
{ 
    // JB/JNAE/JC   CF = 1  Below/not above or equal/carry
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sBELOW,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,   // condition fausse (branche non prise) 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sBELOW,
        IARG_THREAD_ID, 
        IARG_BOOL, true,   // condition VRAIE (branche prise)
        IARG_INST_PTR, IARG_END);
} // cJB

void CONDITIONAL_BR::cJNB(INS &ins) 
{ 
    // JAE/JNB/JNC  CF = 0   Above or equal/not below
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sBELOW,         
        IARG_THREAD_ID, 
        IARG_BOOL,  true,     // INVERSION PAR RAPPORT A JB
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sBELOW,
        IARG_THREAD_ID, 
        IARG_BOOL, false, // INVERSION PAR RAPPORT A JB
        IARG_INST_PTR, IARG_END);
} // cJNB

void CONDITIONAL_BR::cJS(INS &ins) 
{ 
    // JS  SF = 1 Sign (negative)
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSIGN,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,  // condition fausse (branche non prise)
        IARG_INST_PTR, IARG_END);

    INS_InsertCall(ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sSIGN,
        IARG_THREAD_ID, 
        IARG_BOOL, true,      // condition VRAIE (branche prise)
        IARG_INST_PTR, IARG_END);
} // cJS

void CONDITIONAL_BR::cJNS(INS &ins) 
{
    // JNS  SF = 0  Not sign (non-negative)
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSIGN,         
        IARG_THREAD_ID, 
        IARG_BOOL, true, // INVERSION PAR RAPPORT A JS
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sSIGN,
        IARG_THREAD_ID, 
        IARG_BOOL, false, // INVERSION PAR RAPPORT A JS
        IARG_INST_PTR, IARG_END);
} // cJNS

void CONDITIONAL_BR::cJO(INS &ins) 
{ 
    // JO   OF = 1  Overflow
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sOVERFLOW,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,  // condition fausse (branche non prise)
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sOVERFLOW,
        IARG_THREAD_ID, 
        IARG_BOOL, true,   // condition VRAIE (branche prise)
        IARG_INST_PTR, IARG_END);
} // cJO

void CONDITIONAL_BR::cJNO(INS &ins) 
{
    // JNO  OF = 0  Not overflow
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sOVERFLOW,         
        IARG_THREAD_ID, 
        IARG_BOOL, true,   // INVERSION PAR RAPPORT A JO
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sOVERFLOW,
        IARG_THREAD_ID, 
        IARG_BOOL, false,  // INVERSION PAR RAPPORT A JO
        IARG_INST_PTR, IARG_END);
} // cJNO

void CONDITIONAL_BR::cJP(INS &ins) 
{
    // JP/JPE   PF = 1  Parity/parity even
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sPARITY,         
        IARG_THREAD_ID, 
        IARG_BOOL,  false,  // condition fausse (branche non prise)
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sPARITY,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
        IARG_INST_PTR, IARG_END);
} // cJP
       
void CONDITIONAL_BR::cJNP(INS &ins) 
{
    // JNP/JPO  PF = 0    Not parity/parity odd
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sPARITY,         
        IARG_THREAD_ID, 
        IARG_BOOL,   true,  // INVERSION PAR RAPPORT A JP
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sPARITY,
        IARG_THREAD_ID, 
        IARG_BOOL,  false,  // INVERSION PAR RAPPORT A JP
        IARG_INST_PTR, IARG_END);
} // cJNP

void CONDITIONAL_BR::cJZ(INS &ins) 
{ 
    // JE/JZ   ZF = 1  Equal/zero
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sZERO,         
        IARG_THREAD_ID, 
        IARG_BOOL,  false,  // condition fausse (branche non prise)
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sZERO,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
        IARG_INST_PTR, IARG_END);
} // cJZ

void CONDITIONAL_BR::cJNZ(INS &ins) 
{
    // JNE/JNZ  ZF = 0   Not equal/not zero
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sZERO,         
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // INVERSION PAR RAPPORT A JZ
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sZERO,
        IARG_THREAD_ID, 
        IARG_BOOL,  false,  // INVERSION PAR RAPPORT A JZ
        IARG_INST_PTR, IARG_END);
} // cJNZ

void CONDITIONAL_BR::cJBE(INS &ins)
{ 
    // JBE/JNA  (CF or ZF) = 1  Below or equal/not above
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sBELOW_OR_EQUAL,         
        IARG_THREAD_ID, 
        IARG_BOOL,  false,      // Branche non-prise
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sBELOW_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,       // branche prise
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJBE

void CONDITIONAL_BR::cJNBE(INS &ins) 
{
    // JA/JNBE  (CF or ZF) = 0  Above/not below or equal
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sBELOW_OR_EQUAL,         
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // INVERSION PAR RAPPORT A JBE
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sBELOW_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,  false,      // INVERSION PAR RAPPORT A JBE
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJNBE

void CONDITIONAL_BR::cJL(INS &ins) 
{ 
    // JL/JNGE  (SF xor OF) = 1 Less/not greater or equal
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sLESS,
        IARG_THREAD_ID, 
        IARG_BOOL, false,      // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sLESS,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition VRAIE (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJL

void CONDITIONAL_BR::cJNL(INS &ins) 
{
    // JGE/JNL      (SF xor OF) = 0 Greater or equal/not less
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sLESS,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // INVERSION PAR RAPPORT A JL
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sLESS,
        IARG_THREAD_ID, 
        IARG_BOOL,      false,      // INVERSION PAR RAPPORT A JL
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJNL

void CONDITIONAL_BR::cJLE(INS &ins) 
{
    // JLE/JNG  ((SF xor OF) or ZF) = 1 Less or equal/not greater
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sLESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      false,      // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sLESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition VRAIE (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJLE

void CONDITIONAL_BR::cJNLE(INS &ins) 
{
    // JG/JNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sLESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // INVERSION PAR RAPPORT A JLE
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sLESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      false,      // INVERSION PAR RAPPORT A JLE
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJNLE

// SIMULATE

void CONDITIONAL_BR::sBELOW(THREADID tid, bool isTaken, ADDRINT insAddress) 
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JB/JNAE/JC   CF = 1   Below/not above or equal/carry   
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("J(N)B");
        pFormula->addConstraint_BELOW(pTmgrTls, insAddress, isTaken);
    }
} // sBELOW

void CONDITIONAL_BR::sSIGN(THREADID tid, bool isTaken, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JS    SF = 1   Sign (negative)
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("J(N)S");
        pFormula->addConstraint_SIGN(pTmgrTls, insAddress, isTaken);
    }
} // sSIGN

void CONDITIONAL_BR::sOVERFLOW(THREADID tid, bool isTaken, ADDRINT insAddress) 
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JO  OF = 1  Overflow
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT("J(N)O");
        pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, isTaken);
    }
} // sOVERFLOW

void CONDITIONAL_BR::sPARITY(THREADID tid, bool isTaken, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JP/JPE  PF = 1    Parity/parity even
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("J(N)P");
        pFormula->addConstraint_PARITY(pTmgrTls, insAddress, isTaken);
    }
} // sPARITY

void CONDITIONAL_BR::sZERO(THREADID tid, bool isTaken, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JE/JZ    ZF = 1    Equal/zero 
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("J(N)Z");
        pFormula->addConstraint_ZERO(pTmgrTls, insAddress, isTaken);
    }
}

void CONDITIONAL_BR::sBELOW_OR_EQUAL(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // (CF or ZF) = 1  Below or equal/not above
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("J(N)BE");
        pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, isTaken, regEflagsValue);
    }
} // sBELOW_OR_EQUAL

void CONDITIONAL_BR::sLESS(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JL/JNGE   (SF xor OF) = 1 Less/not greater or equal   
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted()) 
    {TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
        _LOGTAINT("J(N)L");
        pFormula->addConstraint_LESS(pTmgrTls, insAddress, isTaken, regEflagsValue);
    }
} // sLESS

void CONDITIONAL_BR::sLESS_OR_EQUAL(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    // JLE/JNG  ((SF xor OF) or ZF) = 1 Less or equal/not greater
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT("J(N)LE");
        pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, isTaken, regEflagsValue);
    }
} // sLESS_OR_EQUAL