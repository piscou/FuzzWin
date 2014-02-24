#include "bitbyte.h"
#include "buildFormula.h"
#include "utils.h"  // démarquage suite à SETcc

/*************/
/*** SETcc ***/
/*************/

//! tous les callbacks pour SETcc suivent le même principe
//! C'est l'une des rares instructions où la fonction d'analyse 
//! sera insérée APRES l'exécution. En effet, SETcc ne fait pas partie des instructions
//! avec prédicats qui utilisent le paramètre IARG_EXECUTING (comme CMOVcc et Jcc)
//! 
//! Dans la conception de PIN, l'instruction est en effet toujours exécutée : elle
//! fixe la destination (registre ou mémoire, 8 bits) à 0 ou 1 selon la valeur du prédicat
//! 
//! Donc instrumentation en IPOINT_AFTER
//! avec passage en arguments de la destination (et des flags selon le type de predicat)
//!
//! la fonction d'analyse lit la valeur de la destination, regarde si le predicat
//! a été vrai (<-> destination à 1), et ajoute la contrainte correspondante
//! ne pas oublier : démarquage destination quoi qu'il arrive

void BITBYTE::cSETB(INS &ins) 
{ 
    // SETB/SETNAE/SETC   CF = 1          Below/not above or equal/carry     
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETB_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETB_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETB

void BITBYTE::cSETNB(INS &ins) 
{ 
    // SETAE/SETNB/SETNC  CF = 0     Above or equal/not below
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNB_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNB_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNB

void BITBYTE::cSETS(INS &ins) 
{ 
    // SETS           SF = 1          Sign (negative)   
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETS_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETS_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETS

void BITBYTE::cSETNS(INS &ins) 
{
    // SETNS          SF = 0          Not sign (non-negative) 
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNS_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNS_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNS

void BITBYTE::cSETO(INS &ins) 
{ 
    // SETO           OF = 1          Overflow  
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETO_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETO_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETO

void BITBYTE::cSETNO(INS &ins) 
{
    // SETNO          OF = 0          Not overflow   
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNO_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNO_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETNO

void BITBYTE::cSETP(INS &ins) 
{
    // SETP/SETPE       PF = 1          Parity/parity even 
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETP_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETP_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETP
       
void BITBYTE::cSETNP(INS &ins) 
{
    // SETNP/SETPO      PF = 0          Not parity/parity odd 
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNP_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNP_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNP

void BITBYTE::cSETZ(INS &ins) 
{ 
    // SETE/SETZ        ZF = 1          Equal/zero
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETZ_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETZ_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETZ

void BITBYTE::cSETNZ(INS &ins) 
{
    // SETNE/SETNZ      ZF = 0          Not equal/not zero
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNZ_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNZ_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNZ

void BITBYTE::cSETBE(INS &ins) 
{ 
    // SETBE/SETNA      (CF or ZF) = 1  Below or equal/not above  
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETBE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETBE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETBE

void BITBYTE::cSETNBE(INS &ins) 
{
    // SETA/SETNBE      (CF or ZF) = 0  Above/not below or equal
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNBE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNBE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNBE

void BITBYTE::cSETL(INS &ins) 
{ 
    // SETL/SETNGE      (SF xor OF) = 1 Less/not greater or equal
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETL_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETL_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETL

void BITBYTE::cSETNL(INS &ins) 
{
    // SETGE/SETNL      (SF xor OF) = 0 Greater or equal/not less
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNL_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNL_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNL

void BITBYTE::cSETLE(INS &ins) 
{
    // SETLE/SETNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETLE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETLE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETLE

void BITBYTE::cSETNLE(INS &ins) 
{
    if (INS_IsMemoryWrite(ins))     
    {   
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNLE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits)
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNLE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits)
            IARG_REG_VALUE, regDest, // sa valeur (qui ser 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETNLE

/*******************/
/****  SIMULATE ****/
/*******************/

// -------------------
// DESTINATION MEMOIRE
// -------------------
void BITBYTE::sSETB_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETB/SETNAE/SETC   CF = 1     Below/not above or equal/carry   
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("SETB_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETB

void BITBYTE::sSETNB_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETAE/SETNB/SETNC  CF = 0     Above or equal/not below
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("SETNB_M");
        // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
        g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNB

void BITBYTE::sSETS_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETS           SF = 1          Sign (negative)
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("SETS_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_SIGN(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETS

void BITBYTE::sSETNS_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNS       SF = 0      Not sign (non-negative)
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("SETNS_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_SIGN(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNS

void BITBYTE::sSETO_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETO           OF = 1          Overflow
    if (pTmgrTls->isOverflowFlagTainted())  
    {
        _LOGTAINT("SETO_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETO

void BITBYTE::sSETNO_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNO           OF = 0          not Overflow
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT("SETNO_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNO

void BITBYTE::sSETP_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETP/SETPE       PF = 1          Parity/parity even
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("SETP_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_PARITY(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETP

void BITBYTE::sSETNP_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNP/SETPO      PF = 0          Not parity/parity odd
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("SETNP_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_PARITY(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNP

void BITBYTE::sSETZ_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETE/SETZ        ZF = 1          Equal/zero
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("SETZ_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_ZERO(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETZ

void BITBYTE::sSETNZ_M(THREADID tid, ADDRINT address, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNE/SETNZ      ZF = 0          Not equal/not zero
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("SETNZ_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_ZERO(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNZ

void BITBYTE::sSETBE_M(THREADID tid, ADDRINT address, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // (CF or ZF) = 1  Below or equal/not above
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT("SETBE_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETBE

void BITBYTE::sSETNBE_M(THREADID tid, ADDRINT address, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETA/SETNBE      (CF or ZF) = 0  Above/not below or equal
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT("SETNBE_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNBE

void BITBYTE::sSETL_M(THREADID tid, ADDRINT address, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETL/SETNGE      (SF xor OF) = 1 Less/not greater or equal
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETL_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_LESS(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETL

void BITBYTE::sSETNL_M(THREADID tid, ADDRINT address, ADDRINT regEflagsValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETGE/SETNL      (SF xor OF) = 0 Greater or equal/not less
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETNL_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_LESS(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNL

void BITBYTE::sSETLE_M(THREADID tid, ADDRINT address, ADDRINT regEflagsValue, ADDRINT insAddress) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETLE/SETNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETLE_M");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, (getMemoryValue<8>(address) != 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETLE

void BITBYTE::sSETNLE_M(THREADID tid, ADDRINT address, ADDRINT regEflagsValue, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETG/SETNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETNLE_M");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, (getMemoryValue<8>(address) == 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrGlobal->unTaintMemory<8>(address);
}// sSETNLE



// --------------------
// DESTINATION REGISTRE
// --------------------

void BITBYTE::sSETB_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETB/SETNAE/SETC   CF = 1     Below/not above or equal/carry   
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("SETB_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress, (regDestValue != 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETB

void BITBYTE::sSETNB_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETAE/SETNB/SETNC  CF = 0     Above or equal/not below
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT("SETNB_R");
        // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
        g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress, (regDestValue == 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNB

void BITBYTE::sSETS_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETS           SF = 1          Sign (negative)
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("SETS_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_SIGN(pTmgrTls, insAddress, (regDestValue != 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETS

void BITBYTE::sSETNS_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNS       SF = 0      Not sign (non-negative)
    if (pTmgrTls->isSignFlagTainted()) 
    {
        _LOGTAINT("SETNS_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_SIGN(pTmgrTls, insAddress, (regDestValue == 0));
    }

    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNS

void BITBYTE::sSETO_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETO           OF = 1          Overflow
    if (pTmgrTls->isOverflowFlagTainted())  
    {
        _LOGTAINT("SETO_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, (regDestValue != 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETO

void BITBYTE::sSETNO_R(THREADID tid,REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNO           OF = 0          not Overflow
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        _LOGTAINT("SETNO_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress, (regDestValue == 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNO

void BITBYTE::sSETP_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETP/SETPE       PF = 1          Parity/parity even
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("SETP_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_PARITY(pTmgrTls, insAddress, (regDestValue != 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETP

void BITBYTE::sSETNP_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNP/SETPO      PF = 0          Not parity/parity odd
    if (pTmgrTls->isParityFlagTainted()) 
    {
        _LOGTAINT("SETNP_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_PARITY(pTmgrTls, insAddress, (regDestValue == 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNP

void BITBYTE::sSETZ_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETE/SETZ        ZF = 1          Equal/zero
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("SETZ_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_ZERO(pTmgrTls, insAddress, (regDestValue != 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETZ

void BITBYTE::sSETNZ_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETNE/SETNZ      ZF = 0          Not equal/not zero
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        _LOGTAINT("SETNZ_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_ZERO(pTmgrTls, insAddress, (regDestValue == 0));
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNZ

void BITBYTE::sSETBE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // (CF or ZF) = 1  Below or equal/not above
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT("SETBE_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, (regDestValue != 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETBE

void BITBYTE::sSETNBE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETA/SETNBE      (CF or ZF) = 0  Above/not below or equal
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        _LOGTAINT("SETNBE_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress, (regDestValue == 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNBE

void BITBYTE::sSETL_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT regEflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETL/SETNGE      (SF xor OF) = 1 Less/not greater or equal
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETL_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_LESS(pTmgrTls, insAddress, (regDestValue != 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETL

void BITBYTE::sSETNL_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT regEflagsValue, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETGE/SETNL      (SF xor OF) = 0 Greater or equal/not less
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETNL_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_LESS(pTmgrTls, insAddress, (regDestValue == 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNL

void BITBYTE::sSETLE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT regEflagsValue, ADDRINT insAddress) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETLE/SETNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETLE_R");
        // prédicat vrai si la destination est non nulle
        g_pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, (regDestValue != 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETLE

void BITBYTE::sSETNLE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT regEflagsValue, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // SETG/SETNLE      ((SF xor OF) or ZF) = 0 Greater/not less or equal
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        _LOGTAINT("SETNLE_R");
        // prédicat vrai si la destination est nulle (inversion car NOT)
        g_pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress, (regDestValue == 0), regEflagsValue);
    }
    // démarquage de la destination (la contrainte sur sa valeur a été enregistrée)
    pTmgrTls->unTaintRegister<8>(regDest);
}// sSETNLE


/************/
/*** BTxx ***/
/************/

void BITBYTE::cBT(INS &ins)
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler
    REG bitIndexReg = INS_OperandReg(ins, 1); // registre servant d'index (ou REG_INVALID())
    
    if (bitIndexReg == REG_INVALID()) // L'index est alors défini par valeur immédiate
    {	
        if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BT_IM
        {
            switch (INS_MemoryOperandSize(ins, 0)) 
            {			
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBT_IM<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBT_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBT_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BT_IR
        { 
            REG testedReg = INS_OperandReg(ins, 0);
            switch (getRegSize(testedReg))
            {
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBT_IR<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBT_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBT_IR<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        }
    }
    else     // index défini par registre
    {	
        UINT32 bitIndexRegSize = getRegSize(bitIndexReg);
        if (!bitIndexRegSize) return; // registre d'index non supporté
        else if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BT_RM
        {
            switch (bitIndexRegSize) 
            {			
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBT_RM<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBT_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBT_RM<64>; break;
                #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BT_RR
        { 
            REG testedReg = INS_OperandReg(ins, 0); // registre a tester
            switch (getRegSize(testedReg))
            {
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBT_RR<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBT_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBT_RR<64>; break;
                #endif 
                default: return; // registre testé non supporté
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_REG_VALUE, testedReg,
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cBT

void BITBYTE::cBTC(INS &ins)
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler
    REG bitIndexReg = INS_OperandReg(ins, 1); // registre servant d'index (ou REG_INVALID())
    
    if (bitIndexReg == REG_INVALID()) // L'index est alors défini par valeur immédiate
    {	
        if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BTC_IM
        {
            switch (INS_MemoryOperandSize(ins, 0)) 
            {			
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBTC_IM<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBTC_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBTC_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BTC_IR
        { 
            REG testedReg = INS_OperandReg(ins, 0);
            switch (getRegSize(testedReg))
            {
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBTC_IR<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBTC_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBTC_IR<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        }
    }
    else     // index défini par registre
    {	
        UINT32 bitIndexRegSize = getRegSize(bitIndexReg);
        if (!bitIndexRegSize) return; // registre d'index non supporté
        else if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BTC_RM
        {
            switch (bitIndexRegSize) 
            {			
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTC_RM<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTC_RM<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTC_RM<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BTC_RR
        { 
            REG testedReg = INS_OperandReg(ins, 0); // registre a tester
            switch (getRegSize(testedReg))
            {
            case 0: return; // registre testé non supporté
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTC_RR<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTC_RR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTC_RR<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_REG_VALUE, testedReg,
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cBTC

void BITBYTE::cBTR(INS &ins)
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler
    REG bitIndexReg = INS_OperandReg(ins, 1); // registre servant d'index (ou REG_INVALID())
    
    if (bitIndexReg == REG_INVALID()) // L'index est alors défini par valeur immédiate
    {	
        if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BTR_IM
        {
            switch (INS_MemoryOperandSize(ins, 0)) 
            {			
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTR_IM<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTR_IM<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTR_IM<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BTR_IR
        { 
            REG testedReg = INS_OperandReg(ins, 0);
            switch (getRegSize(testedReg))
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTR_IR<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTR_IR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTR_IR<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        }
    }
    else     // index défini par registre
    {	
        UINT32 bitIndexRegSize = getRegSize(bitIndexReg);
        if (!bitIndexRegSize) return; // registre d'index non supporté
        else if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BTR_RM
        {
            switch (bitIndexRegSize) 
            {			
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTR_RM<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTR_RM<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTR_RM<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BTR_RR
        { 
            REG testedReg = INS_OperandReg(ins, 0); // registre a tester
            switch (getRegSize(testedReg))
            {
            case 0: return; // registre testé non supporté
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTR_RR<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTR_RR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTR_RR<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_REG_VALUE, testedReg,
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cBTR

void BITBYTE::cBTS(INS &ins)
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler
    REG bitIndexReg = INS_OperandReg(ins, 1); // registre servant d'index (ou REG_INVALID())
    
    if (bitIndexReg == REG_INVALID()) // L'index est alors défini par valeur immédiate
    {	
        if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BTS_IM
        {
            switch (INS_MemoryOperandSize(ins, 0)) 
            {			
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTS_IM<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTS_IM<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTS_IM<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BTS_IR
        { 
            REG testedReg = INS_OperandReg(ins, 0);
            switch (getRegSize(testedReg))
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBTS_IR<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBTS_IR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBTS_IR<64>; break;
            #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1), // Si non casté, plante en 32bit!!
                CALLBACK_DEBUG IARG_END);
        }
    }
    else     // index défini par registre
    {	
        UINT32 bitIndexRegSize = getRegSize(bitIndexReg);
        if (!bitIndexRegSize) return; // registre d'index non supporté
        else if (INS_OperandIsMemory(ins, 0)) // test de la mémoire : BTS_RM
        {
            switch (bitIndexRegSize) 
            {			
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBTS_RM<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBTS_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBTS_RM<64>; break;
                #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,  
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        } 
        else // test d'un registre : BTS_RR
        { 
            REG testedReg = INS_OperandReg(ins, 0); // registre a tester
            switch (getRegSize(testedReg))
            {
                case 0: return; // registre testé non supporté
                // case 1:	impossible
                case 2:	callback = (AFUNPTR) BITBYTE::sBTS_RR<16>; break;
                case 4:	callback = (AFUNPTR) BITBYTE::sBTS_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) BITBYTE::sBTS_RR<64>; break;
                #endif
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, testedReg,   
                IARG_REG_VALUE, testedReg,
                IARG_UINT32, bitIndexReg,
                IARG_REG_VALUE, bitIndexReg,
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cBTS

void BITBYTE::cBSR(INS &ins)
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler
    REG resultReg = INS_OperandReg(ins, 0); // registre contenant la position du bit trouvé
    UINT32 resultRegSize = getRegSize(resultReg);

    if (!resultRegSize) return; // registre non suivi
    else if (INS_IsMemoryRead(ins)) // test de la mémoire : BSR_M
    {
        switch (resultRegSize) 
        {			
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBSR_M<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBSR_M<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBSR_M<64>; break;
            #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,  
            IARG_UINT32, resultReg,
            CALLBACK_DEBUG IARG_END);
    } 
    else // test d'un registre : BSR_R
    { 
        REG testedReg = INS_OperandReg(ins, 1);
        switch (resultRegSize)
        {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBSR_R<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBSR_R<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBSR_R<64>; break;
            #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, testedReg,
            IARG_REG_VALUE, testedReg,
            IARG_UINT32, resultReg,
            CALLBACK_DEBUG IARG_END);
    }
} // cBSR

void BITBYTE::cBSF(INS &ins)
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler
    REG resultReg = INS_OperandReg(ins, 0); // registre contenant la position du bit trouvé
    UINT32 resultRegSize = getRegSize(resultReg);

    if (!resultRegSize) return; // registre non suivi
    else if (INS_IsMemoryRead(ins)) // test de la mémoire : BSF_M
    {
        switch (resultRegSize) 
        {			
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBSF_M<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBSF_M<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBSF_M<64>; break;
            #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,  
            IARG_UINT32, resultReg,
            CALLBACK_DEBUG IARG_END);
    } 
    else // test d'un registre : BSF_R
    { 
        REG testedReg = INS_OperandReg(ins, 1);
        switch (resultRegSize)
        {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) BITBYTE::sBSF_R<16>; break;
            case 4:	callback = (AFUNPTR) BITBYTE::sBSF_R<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) BITBYTE::sBSF_R<64>; break;
            #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, testedReg,   
            IARG_REG_VALUE, testedReg,
            IARG_UINT32, resultReg,
            CALLBACK_DEBUG IARG_END);
    }
} // cBSF