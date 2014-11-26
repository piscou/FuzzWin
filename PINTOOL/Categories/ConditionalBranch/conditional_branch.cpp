#include "conditional_branch.h"
#include <Translate\translate.h>

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
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_BELOW,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,   // condition fausse (branche non prise) 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_BELOW,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
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
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_SIGN,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,   // condition fausse (branche non prise) 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_SIGN,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
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
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_OVERFLOW,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,   // condition fausse (branche non prise) 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_OVERFLOW,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
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
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_PARITY,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,   // condition fausse (branche non prise) 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_PARITY,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
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
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_ZERO,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,   // condition fausse (branche non prise) 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_ZERO,
        IARG_THREAD_ID, 
        IARG_BOOL,  true,   // condition VRAIE (branche prise)
        IARG_INST_PTR, IARG_END);
} // cJNZ

void CONDITIONAL_BR::cJBE(INS &ins)
{ 
    // JBE/JNA  (CF or ZF) = 1  Below or equal/not above
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sBELOW_OR_EQUAL,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,           // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sBELOW_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJBE

void CONDITIONAL_BR::cJNBE(INS &ins) 
{
    // JA/JNBE  (CF or ZF) = 0  Above/not below or equal
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_BELOW_OR_EQUAL,         
        IARG_THREAD_ID, 
        IARG_BOOL, false,           // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_BELOW_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJNBE

void CONDITIONAL_BR::cJL(INS &ins) 
{ 
    // JL/JNGE  (SF xor OF) = 1 Less/not greater or equal
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sLESS,
        IARG_THREAD_ID, 
        IARG_BOOL, false,           // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sLESS,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJL

void CONDITIONAL_BR::cJNL(INS &ins) 
{
    // JGE/JNL      (SF xor OF) = 0 Greater or equal/not less
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_LESS,
        IARG_THREAD_ID, 
        IARG_BOOL, false,           // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_LESS,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJNL

void CONDITIONAL_BR::cJLE(INS &ins) 
{
    // JLE/JNG  ((SF xor OF) or ZF) = 1 Less or equal/not greater
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sLESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL, false,           // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sLESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJLE

void CONDITIONAL_BR::cJNLE(INS &ins) 
{
    // JG/JNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal
    INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sNOT_LESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL, false,           // condition fausse (branche non prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, (AFUNPTR) sNOT_LESS_OR_EQUAL,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR, IARG_END);
} // cJNLE

void CONDITIONAL_BR::cJRCXZ(INS &ins) 
{
    // JRCXZ : test si CX/ECX/RCX est nul
    REG testedReg = INS_RegR(ins, 0); // pour calcul de la taille de l'instruction
    void (*callback)() = nullptr;

    switch (getRegSize(testedReg))
    {
    // case 1: impossible
    case 2: callback = (AFUNPTR) sJRCXZ<16>; break;
    case 4: callback = (AFUNPTR) sJRCXZ<32>; break;
#if TARGET_IA32E
    case 8: callback = (AFUNPTR) sJRCXZ<64>; break;
#endif
    default: return;
    }

    INS_InsertCall (ins, IPOINT_AFTER, callback,
        IARG_THREAD_ID, 
        IARG_BOOL, false,          // condition fausse (branche non prise)
        IARG_REG_VALUE, testedReg, // valeur de CX/ECX/RCX
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, callback,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,      // condition vraie (branche prise)
        IARG_REG_VALUE, testedReg, // valeur de CX/ECX/RCX
        IARG_INST_PTR, IARG_END);
} // cJRCXZ

/************/
/*** LOOP ***/
/************/

// l'instruction LOOP n'est pas considérée comme "predicated" par PIN
// en effet, quoi qu'il arrive CX/ECX/RCX sera décrémenté de 1
// donc l'instruction est TOUJOURS exécutée.
// traitement à l'identique de Jcc, avec des contraintes sur la valeur de ECX
// et / ou du zéro flag


void CONDITIONAL_BR::cLOOP(INS &ins) 
{ 
    REG testedReg = INS_RegR(ins, 0); // pour calcul de la taille de l'instruction
    void (*callback)() = nullptr;

    switch (getRegSize(testedReg))
    {
    // case 1: impossible
    case 2: callback = (AFUNPTR) sLOOP<16>; break;
    case 4: callback = (AFUNPTR) sLOOP<32>; break;
#if TARGET_IA32E
    case 8: callback = (AFUNPTR) sLOOP<64>; break;
#endif
    default: return;
    }

    // LOOP SIMPLE : test de la valeur du compteur (CX/ECX/RCX)
    INS_InsertCall (ins, IPOINT_AFTER, callback,
        IARG_THREAD_ID, 
        IARG_BOOL, false,          // condition fausse (branche non prise)
        IARG_REG_VALUE, testedReg, // valeur de CX/ECX/RCX
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, callback,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,      // condition vraie (branche prise)
        IARG_REG_VALUE, testedReg, // valeur de CX/ECX/RCX
        IARG_INST_PTR, IARG_END);
} // cLOOP

void CONDITIONAL_BR::cLOOPE(INS &ins) 
{ 
    REG testedReg = INS_RegR(ins, 0); // pour calcul de la taille de l'instruction
    void (*callback)() = nullptr;

    switch (getRegSize(testedReg))
    {
    // case 1: impossible
    case 2: callback = (AFUNPTR) sLOOPE<16>; break;
    case 4: callback = (AFUNPTR) sLOOPE<32>; break;
#if TARGET_IA32E
    case 8: callback = (AFUNPTR) sLOOPE<64>; break;
#endif
    default: return;
    }

    // LOOPE : test de la valeur du compteur (CX/ECX/RCX) + zero Flag
    INS_InsertCall (ins, IPOINT_AFTER, callback,
        IARG_THREAD_ID, 
        IARG_BOOL,      false,      // condition fausse (branche non prise)
        IARG_REG_VALUE, testedReg,  // valeur de CX/ECX/RCX
        IARG_REG_VALUE, REG_GFLAGS, // valeur des FLAGS
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, callback,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, testedReg,  // valeur de CX/ECX/RCX
        IARG_REG_VALUE, REG_GFLAGS, // valeur des FLAGS
        IARG_INST_PTR, IARG_END);
} // cLOOPE

void CONDITIONAL_BR::cLOOPNE(INS &ins) 
{ 
    REG testedReg = INS_RegR(ins, 0); // pour calcul de la taille de l'instruction
    void (*callback)() = nullptr;

    switch (getRegSize(testedReg))
    {
    // case 1: impossible
    case 2: callback = (AFUNPTR) sLOOPNE<16>; break;
    case 4: callback = (AFUNPTR) sLOOPNE<32>; break;
#if TARGET_IA32E
    case 8: callback = (AFUNPTR) sLOOPNE<64>; break;
#endif
    default: return;
    }

    // LOOPNE : test de la valeur du compteur (CX/ECX/RCX) + valeur zero flag
    INS_InsertCall (ins, IPOINT_AFTER, callback,
        IARG_THREAD_ID, 
        IARG_BOOL,      false,      // condition fausse (branche non prise)
        IARG_REG_VALUE, testedReg,  // valeur de CX/ECX/RCX
        IARG_REG_VALUE, REG_GFLAGS, // valeur des FLAGS
        IARG_INST_PTR, IARG_END);

    INS_InsertCall (ins, IPOINT_TAKEN_BRANCH, callback,
        IARG_THREAD_ID, 
        IARG_BOOL,      true,       // condition vraie (branche prise)
        IARG_REG_VALUE, testedReg,  // valeur de CX/ECX/RCX
        IARG_REG_VALUE, REG_GFLAGS, // valeur des FLAGS
        IARG_INST_PTR, IARG_END);
} // cLOOPNE

/****************/
/*** SIMULATE ***/
/****************/

void CONDITIONAL_BR::sBELOW(THREADID tid, bool isTaken, ADDRINT insAddress) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JB/JNAE/JC   CF = 1   Below/not above or equal/carry   
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JB");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_BELOW, isTaken, insAddress);
    }
} // sBELOW

void CONDITIONAL_BR::sSIGN(THREADID tid, bool isTaken, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JS    SF = 1   Sign (negative)
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JS");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_SIGN, isTaken, insAddress);
    }
} // sSIGN

void CONDITIONAL_BR::sOVERFLOW(THREADID tid, bool isTaken, ADDRINT insAddress) 
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JO  OF = 1  Overflow
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JO");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_OVERFLOW, isTaken, insAddress);
    }
} // sOVERFLOW

void CONDITIONAL_BR::sPARITY(THREADID tid, bool isTaken, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JP/JPE  PF = 1    Parity/parity even
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JP");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_PARITY, isTaken, insAddress);
    }
} // sPARITY

void CONDITIONAL_BR::sZERO(THREADID tid, bool isTaken, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JE/JZ    ZF = 1    Equal/zero 
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JZ");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_ZERO, isTaken, insAddress);
    }
}

void CONDITIONAL_BR::sBELOW_OR_EQUAL(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // (CF or ZF) = 1  Below or equal/not above
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JBE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_BELOW_OR_EQUAL, isTaken, insAddress, regEflagsValue);
    }
} // sBELOW_OR_EQUAL

void CONDITIONAL_BR::sLESS(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JL/JNGE   (SF xor OF) = 1 Less/not greater or equal   
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted()) 
    {TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
        _LOGTAINT(tid, insAddress, "JL");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_LESS, isTaken, insAddress, regEflagsValue);
    }
} // sLESS

void CONDITIONAL_BR::sLESS_OR_EQUAL(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // JLE/JNG  ((SF xor OF) or ZF) = 1 Less or equal/not greater
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JLE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_LESS_OR_EQUAL, isTaken, insAddress, regEflagsValue);
    }
} // sLESS_OR_EQUAL

/**************************/
/*** VERSIONS INVERSEES ***/
/**************************/

void CONDITIONAL_BR::sNOT_BELOW(THREADID tid, bool isTaken, ADDRINT insAddress) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);  
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNB");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_BELOW, isTaken, insAddress);
    }
} // sNOT_BELOW

void CONDITIONAL_BR::sNOT_SIGN(THREADID tid, bool isTaken, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNS");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_SIGN, isTaken, insAddress);
    }
} // sNOT_SIGN

void CONDITIONAL_BR::sNOT_OVERFLOW(THREADID tid, bool isTaken, ADDRINT insAddress) 
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNO");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_OVERFLOW, isTaken, insAddress);
    }
} // sNOT_OVERFLOW

void CONDITIONAL_BR::sNOT_PARITY(THREADID tid, bool isTaken, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNP");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_PARITY, isTaken, insAddress);
    }
} // sNOT_PARITY

void CONDITIONAL_BR::sNOT_ZERO(THREADID tid, bool isTaken, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNZ");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_ZERO, isTaken, insAddress);
    }
}

void CONDITIONAL_BR::sNOT_BELOW_OR_EQUAL(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNBE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_BELOW_OR_EQUAL, isTaken, insAddress, regEflagsValue);
    }
} // sNOT_BELOW_OR_EQUAL

void CONDITIONAL_BR::sNOT_LESS(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid); 
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted()) 
    {
        TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
        _LOGTAINT(tid, insAddress, "JNL");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_LESS, isTaken, insAddress, regEflagsValue);
    }
} // sNOT_LESS

void CONDITIONAL_BR::sNOT_LESS_OR_EQUAL(THREADID tid, bool isTaken, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "JNLE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_LESS_OR_EQUAL, isTaken, insAddress, regEflagsValue);
    }
} // sNOT_LESS_OR_EQUAL
