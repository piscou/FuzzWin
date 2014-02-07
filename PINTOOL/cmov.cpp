#include "CMOV.h"
#include "buildFormula.h"
#include "DATAXFER.h"

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
//! Pas la peine de tester le marquage du regsitre source en amont
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
            CALLBACK_DEBUG IARG_END);
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
            CALLBACK_DEBUG IARG_END);
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
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("CMOVB");
        pFormula->addConstraint_BELOW(pTmgrTls, insAddress, isPredicatTrue);
    }
}// sCMOVB

void CMOV::sCMOVNB(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVAE/CMOVNB/CMOVNC  CF = 0     Above or equal/not below
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("CMOVNB");
        pFormula->addConstraint_BELOW(pTmgrTls, insAddress, !(isPredicatTrue));
    }
}// sCMOVNB

void CMOV::sCMOVS(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVS           SF = 1          Sign (negative)
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("CMOVS");
        pFormula->addConstraint_SIGN(pTmgrTls, insAddress, isPredicatTrue);
    }
}// sCMOVS

void CMOV::sCMOVNS(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVNS       SF = 0      Not sign (non-negative)
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("CMOVNS");
        pFormula->addConstraint_SIGN(pTmgrTls, insAddress, !(isPredicatTrue));
    }
}// sCMOVNS

void CMOV::sCMOVO (THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVO           OF = 1          Overflow
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isOverflowFlagTainted())  
    {
        _LOGTAINT("CMOVO");
        pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, isPredicatTrue);
    }
}// sCMOVO

void CMOV::sCMOVNO(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVNO           OF = 0          not Overflow
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT("CMOVNO");
        pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, !(isPredicatTrue));
    }
}// sCMOVNO

void CMOV::sCMOVP (THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVP/CMOVPE       PF = 1          Parity/parity even
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("CMOVP");
        pFormula->addConstraint_PARITY(pTmgrTls, insAddress, isPredicatTrue);
    }
}// sCMOVP

void CMOV::sCMOVNP(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVNP/CMOVPO      PF = 0          Not parity/parity odd
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("CMOVNP");
        pFormula->addConstraint_PARITY(pTmgrTls, insAddress, !(isPredicatTrue));
    }
}// sCMOVNP

void CMOV::sCMOVZ (THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{ 
    // CMOVE/CMOVZ        ZF = 1          Equal/zero
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("CMOVZ");
        pFormula->addConstraint_ZERO(pTmgrTls, insAddress, isPredicatTrue);
    }
}// sCMOVZ

void CMOV::sCMOVNZ(THREADID tid, bool isPredicatTrue, ADDRINT insAddress)
{
    // CMOVNE/CMOVNZ      ZF = 0          Not equal/not zero
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("CMOVNZ");
        pFormula->addConstraint_ZERO(pTmgrTls, insAddress, !(isPredicatTrue));
    }
}// sCMOVNZ

void CMOV::sCMOVBE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    // (CF or ZF) = 1  Below or equal/not above
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT("CMOVBE");
        pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, isPredicatTrue, regEflagsValue);
    }
}// sCMOVBE

void CMOV::sCMOVNBE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    // CMOVA/CMOVNBE      (CF or ZF) = 0  Above/not below or equal
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT("CMOVNBE");
        pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, !(isPredicatTrue), regEflagsValue);
    }
}// sCMOVNBE

void CMOV::sCMOVL(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    // CMOVL/CMOVNGE      (SF xor OF) = 1 Less/not greater or equal
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("CMOVL");
        pFormula->addConstraint_LESS(pTmgrTls, insAddress, isPredicatTrue, regEflagsValue);
    }
}// sCMOVL

void CMOV::sCMOVNL(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress)
{ 
    // CMOVGE/CMOVNL      (SF xor OF) = 0 Greater or equal/not less
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("CMOVNL");
        pFormula->addConstraint_LESS(pTmgrTls, insAddress, !(isPredicatTrue), regEflagsValue);
    }
}// sCMOVNL

void CMOV::sCMOVLE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress) 
{ 
    // CMOVLE/CMOVNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("CMOVLE");
        pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, isPredicatTrue, regEflagsValue);
    }
}// sCMOVLE

void CMOV::sCMOVNLE(THREADID tid, bool isPredicatTrue, ADDRINT regEflagsValue, ADDRINT insAddress) 
{
    // CMOVG/CMOVNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("CMOVNLE");
        pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, !(isPredicatTrue), regEflagsValue);
    }
}// sCMOVNLE
