#include "cmov.h"
#include <Dataxfer\dataxfer.h>

//! tous les callbacks pour CMOV suivent le même principe
//! 1- détermination de la source (mémoire ou registre)
//! la destination étant toujours un registre
//! 
//! 2- "InsertCall", avec en paramètres IARG_EXECUTING (condition vraie ou fausse) et les flags 
//! Si flags marqués, enregistrement de la contrainte associé pour inversion
//! 
//! 3- appel à la procédure "cIfPredicated_CMOVcc", commune à tous les CMOV
//! elle insère un "InsertPredicatedCall", appelant un MOVMR ou RR si
//! le predicat est vrai (simulation exacte du comportement de CMOV)
//!
//! Pas la peine de tester le marquage du registre source en amont
//! seul importe la valeur du predicat
void CMOV::cIfPredicated_CMOVcc(INS &ins) 
{
    void (*callback)() = nullptr;

    REG regDest  = INS_OperandReg(ins, 0);
    UINT32 regDestSize = getRegSize(regDest);
    if (!regDestSize) return; // registre destination non suivi

    else if (INS_IsMemoryRead(ins)) // Mémoire -> Reg (MOVRM) si predicat vrai
    {   
        switch (regDestSize)
        { 
        //case 1:   impossible pour CMOV
        case 2: callback = (AFUNPTR) DATAXFER::sMOV_MR<16>; break;
        case 4: callback = (AFUNPTR) DATAXFER::sMOV_MR<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) DATAXFER::sMOV_MR<64>; break;
        #endif
        }

        // seulement si le predicat est vrai:
        INS_InsertPredicatedCall (ins, IPOINT_BEFORE, (AFUNPTR) callback, 
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,    
            IARG_UINT32, regDest, 
            IARG_INST_PTR, IARG_END);
    }
    else 
    {    // registre -> registre = MOVRR si predicat vrai
        REG regSrc  = INS_OperandReg(ins, 1);
        switch (getRegSize(regSrc))  // taille du registre source
        {
        case 0 : return; // registre source non suivi
        // case 1:   impossible pour CMOV
        case 2: callback = (AFUNPTR) DATAXFER::sMOV_RR<16>; break;
        case 4: callback = (AFUNPTR) DATAXFER::sMOV_RR<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) DATAXFER::sMOV_RR<64>; break;
        #endif
        }
            
        // seulement si le predicat est vrai:
        INS_InsertPredicatedCall (ins, IPOINT_BEFORE, (AFUNPTR) callback, 
            IARG_THREAD_ID,
            IARG_UINT32, regSrc,    // registre source
            IARG_UINT32, regDest,   // registre destination
            IARG_INST_PTR, IARG_END);
    }
}// cIfPredicated_CMOVcc

void CMOV::cCMOVB(INS &ins) 
{ 
    // CMOVB/CMOVNAE/CMOVC   CF = 1          Below/not above or equal/carry     
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVB,         
        IARG_THREAD_ID,
        IARG_EXECUTING,         // vraie si condition remplie, faux autrement
        IARG_INST_PTR,          // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins); 
}// cCMOVB

void CMOV::cCMOVNB(INS &ins) 
{ 
    // CMOVAE/CMOVNB/CMOVNC  CF = 0     Above or equal/not below
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNB,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNB

void CMOV::cCMOVS(INS &ins) 
{ 
    // CMOVS           SF = 1          Sign (negative)   
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVS,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVS

void CMOV::cCMOVNS(INS &ins) 
{
    // CMOVNS          SF = 0          Not sign (non-negative) 
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNS,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNS

void CMOV::cCMOVO(INS &ins) 
{ 
    // CMOVO           OF = 1          Overflow  
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVO,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVO

void CMOV::cCMOVNO(INS &ins) 
{
    // CMOVNO          OF = 0          Not overflow   
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNO,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNO

void CMOV::cCMOVP(INS &ins) 
{
    // CMOVP/CMOVPE       PF = 1          Parity/parity even 
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVP,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVP
       
void CMOV::cCMOVNP(INS &ins) 
{
    // CMOVNP/CMOVPO      PF = 0          Not parity/parity odd 
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNP,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNP

void CMOV::cCMOVZ(INS &ins) 
{ 
    // CMOVE/CMOVZ        ZF = 1          Equal/zero
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVZ,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVZ

void CMOV::cCMOVNZ(INS &ins) 
{
    // CMOVNE/CMOVNZ      ZF = 0          Not equal/not zero
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNZ,         
        IARG_THREAD_ID,
        IARG_EXECUTING, // vraie si condition remplie, faux autrement
        IARG_INST_PTR,  // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNZ

void CMOV::cCMOVBE(INS &ins) 
{ 
    // CMOVBE/CMOVNA      (CF or ZF) = 1  Below or equal/not above  
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVBE,         
        IARG_THREAD_ID,
        IARG_EXECUTING,     // vraie si condition remplie, faux autrement
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR,      // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVBE

void CMOV::cCMOVNBE(INS &ins) 
{
    // CMOVA/CMOVNBE      (CF or ZF) = 0  Above/not below or equal
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNBE,         
        IARG_THREAD_ID,
        IARG_EXECUTING,     // vraie si condition remplie, faux autrement
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR,      // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNBE

void CMOV::cCMOVL(INS &ins) 
{ 
    // CMOVL/CMOVNGE      (SF xor OF) = 1 Less/not greater or equal
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVL,         
        IARG_THREAD_ID,
        IARG_EXECUTING,     // vraie si condition remplie, faux autrement
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR,      // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVL

void CMOV::cCMOVNL(INS &ins) 
{
    // CMOVGE/CMOVNL      (SF xor OF) = 0 Greater or equal/not less
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNL,         
        IARG_THREAD_ID,
        IARG_EXECUTING,     // vraie si condition remplie, faux autrement
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR,      // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNL

void CMOV::cCMOVLE(INS &ins) 
{
    // CMOVLE/CMOVNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVLE,         
        IARG_THREAD_ID,
        IARG_EXECUTING,     // vraie si condition remplie, faux autrement
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR,      // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVLE

void CMOV::cCMOVNLE(INS &ins) 
{
    // CMOVG/CMOVNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal 
    // dans tous les cas
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMOVNLE,         
        IARG_THREAD_ID,
        IARG_EXECUTING,     // vraie si condition remplie, faux autrement
        IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
        IARG_INST_PTR,      // adresse de l'instruction
        IARG_END);

    // simulation du MOV si le predicat s'avère vrai
    cIfPredicated_CMOVcc(ins);
}// cCMOVNLE


// SIMULATE
void CMOV::sCMOVB(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVB/CMOVNAE/CMOVC   CF = 1     Below/not above or equal/carry   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVB");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_BELOW, isPredicatTrue, insAddress);
    }
}// sCMOVB

void CMOV::sCMOVNB(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVAE/CMOVNB/CMOVNC  CF = 0     Above or equal/not below
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNB");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_BELOW, isPredicatTrue, insAddress);
    }
}// sCMOVNB

void CMOV::sCMOVS(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVS           SF = 1          Sign (negative)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVS");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_SIGN, isPredicatTrue, insAddress);
    }
}// sCMOVS

void CMOV::sCMOVNS(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVNS       SF = 0      Not sign (non-negative)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNS");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_SIGN, isPredicatTrue, insAddress);
    }
}// sCMOVNS

void CMOV::sCMOVO (THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVO           OF = 1          Overflow
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isOverflowFlagTainted())  
    {
        _LOGTAINT(tid, insAddress, "CMOVO");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_OVERFLOW, isPredicatTrue, insAddress);
    }
}// sCMOVO

void CMOV::sCMOVNO(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVNO           OF = 0          not Overflow
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNO");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_OVERFLOW, isPredicatTrue, insAddress);
    }
}// sCMOVNO

void CMOV::sCMOVP (THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVP/CMOVPE       PF = 1          Parity/parity even
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVP");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_PARITY, isPredicatTrue, insAddress);
    }
}// sCMOVP

void CMOV::sCMOVNP(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVNP/CMOVPO      PF = 0          Not parity/parity odd
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNP");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_PARITY, isPredicatTrue, insAddress);
    }
}// sCMOVNP

void CMOV::sCMOVZ (THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVE/CMOVZ        ZF = 1          Equal/zero
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVZ");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_ZERO, isPredicatTrue, insAddress);
    }
}// sCMOVZ

void CMOV::sCMOVNZ(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVNE/CMOVNZ      ZF = 0          Not equal/not zero
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNZ");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_ZERO, isPredicatTrue, insAddress);
    }
}// sCMOVNZ

void CMOV::sCMOVBE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    // (CF or ZF) = 1  Below or equal/not above
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT(tid, insAddress, "CMOVBE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_BELOW_OR_EQUAL, isPredicatTrue, insAddress, regEflagsValue);
    }
}// sCMOVBE

void CMOV::sCMOVNBE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    // CMOVA/CMOVNBE      (CF or ZF) = 0  Above/not below or equal
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNBE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_BELOW_OR_EQUAL, isPredicatTrue, insAddress, regEflagsValue);
    }
}// sCMOVNBE

void CMOV::sCMOVL(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    // CMOVL/CMOVNGE      (SF xor OF) = 1 Less/not greater or equal
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT(tid, insAddress, "CMOVL");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_LESS, isPredicatTrue, insAddress, regEflagsValue);
    }
}// sCMOVL

void CMOV::sCMOVNL(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{ 
    // CMOVGE/CMOVNL      (SF xor OF) = 0 Greater or equal/not less
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNL");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_LESS, isPredicatTrue, insAddress, regEflagsValue);
    }
}// sCMOVNL

void CMOV::sCMOVLE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress) 
{ 
    // CMOVLE/CMOVNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT(tid, insAddress, "CMOVLE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_LESS_OR_EQUAL, isPredicatTrue, insAddress, regEflagsValue);
    }
}// sCMOVLE

void CMOV::sCMOVNLE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress) 
{
    // CMOVG/CMOVNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT(tid, insAddress, "CMOVNLE");
        g_pFormula->addConstraintJcc(pTmgrTls, PREDICATE_NOT_LESS_OR_EQUAL, isPredicatTrue, insAddress, regEflagsValue);
    }
}// sCMOVNLE
