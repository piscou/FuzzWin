#include "bitbyte.h"

/*************/
/*** SETcc ***/
/*************/

//! tous les callbacks pour SETcc suivent le même principe 
//! SETcc ne fait pas partie des instructions avec prédicats 
//! qui utilisent le paramètre IARG_EXECUTING (comme CMOVcc et Jcc)
//! Dans la conception de PIN, l'instruction est en effet toujours exécutée : elle
//! fixe la destination (registre ou mémoire, 8 bits) à 0 ou 1 selon la valeur du prédicat
//! 
//! SETcc fonctionne à l'identique d'un opérateur ternaire en C
//! selon la valeur des flags, la destination vaudra 1 (prédicat vrai) ou 0 (prédicat faux
//! bien que la destination soit une valeur numérique, celle-ci dépend des flags s'ils sont marqués !!
//!
//! la relation corespondante est X_SETCC avec pour parametres:
//!   1- le type de predicat (enum PREDICATE)
//!   2- le premier flag concerné (valeur ou variable)
//!   3- les autres flags, si besoin

void BITBYTE::cSETB(INS &ins) 
{ 
    // SETB/SETNAE/SETC   CF = 1          Below/not above or equal/carry     
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETB_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {  
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETB_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETB

void BITBYTE::cSETNB(INS &ins) 
{ 
    // SETAE/SETNB/SETNC  CF = 0     Above or equal/not below
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNB_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNB_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETNB

void BITBYTE::cSETS(INS &ins) 
{ 
    // SETS           SF = 1          Sign (negative)   
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETS_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    { 
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETS_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETS

void BITBYTE::cSETNS(INS &ins) 
{
    // SETNS          SF = 0          Not sign (non-negative) 
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNS_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {  
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNS_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETNS

void BITBYTE::cSETO(INS &ins) 
{ 
    // SETO           OF = 1          Overflow  
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETO_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    { 
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETO_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETO

void BITBYTE::cSETNO(INS &ins) 
{
    // SETNO          OF = 0          Not overflow   
       if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNO_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {  
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNO_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    } 
}// cSETNO

void BITBYTE::cSETP(INS &ins) 
{
    // SETP/SETPE       PF = 1          Parity/parity even 
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETP_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {  
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETP_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    } 
}// cSETP
       
void BITBYTE::cSETNP(INS &ins) 
{
    // SETNP/SETPO      PF = 0          Not parity/parity odd 
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNP_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {  
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNP_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETNP

void BITBYTE::cSETZ(INS &ins) 
{ 
    // SETE/SETZ        ZF = 1          Equal/zero
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETZ_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    { 
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETZ_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETZ

void BITBYTE::cSETNZ(INS &ins) 
{
    // SETNE/SETNZ      ZF = 0          Not equal/not zero
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNZ_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNZ_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_INST_PTR, IARG_END);
    }
}// cSETNZ

void BITBYTE::cSETBE(INS &ins) 
{ 
    // SETBE/SETNA      (CF or ZF) = 1  Below or equal/not above  
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETBE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETBE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
}// cSETBE

void BITBYTE::cSETNBE(INS &ins) 
{
    // SETA/SETNBE      (CF or ZF) = 0  Above/not below or equal
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNBE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNBE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
}// cSETNBE

void BITBYTE::cSETL(INS &ins) 
{ 
    // SETL/SETNGE      (SF xor OF) = 1 Less/not greater or equal
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETL_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETL_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
}// cSETL

void BITBYTE::cSETNL(INS &ins) 
{
    // SETGE/SETNL      (SF xor OF) = 0 Greater or equal/not less
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNL_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNL_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
}// cSETNL

void BITBYTE::cSETLE(INS &ins) 
{
    // SETLE/SETNG      ((SF xor OF) or ZF) = 1 Less or equal/not greater
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETLE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETLE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    } 
}// cSETLE

void BITBYTE::cSETNLE(INS &ins) 
{
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETNLE_M,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    }
    else // forcement registre
    {
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNLE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR, IARG_END);
    } 
}// cSETNLE

/*******************/
/****  SIMULATE ****/
/*******************/

// --------------------
// destination mémoire 
// ---------------------

void BITBYTE::sSETB_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isCarryFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_BELOW),
            ObjectSource(pTmgrTls->getTaintCarryFlag())));
    }   
}// sSETB_M

void BITBYTE::sSETNB_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isCarryFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_BELOW),
            ObjectSource(pTmgrTls->getTaintCarryFlag())));
    }   
}// sSETNB_M

void BITBYTE::sSETS_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isSignFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_SIGN),
            ObjectSource(pTmgrTls->getTaintSignFlag())));
    }   
}// sSETS_M

void BITBYTE::sSETNS_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isSignFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_SIGN),
            ObjectSource(pTmgrTls->getTaintSignFlag())));
    }   
}// sSETS_M

void BITBYTE::sSETO_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isOverflowFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_OVERFLOW),
            ObjectSource(pTmgrTls->getTaintOverflowFlag())));
    }   
}// sSETO_M

void BITBYTE::sSETNO_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isOverflowFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_OVERFLOW),
            ObjectSource(pTmgrTls->getTaintOverflowFlag())));
    }   
}// sSETNO_M

void BITBYTE::sSETP_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isParityFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_PARITY),
            ObjectSource(pTmgrTls->getTaintParityFlag())));
    }   
}// sSETP_M

void BITBYTE::sSETNP_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isParityFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_PARITY),
            ObjectSource(pTmgrTls->getTaintParityFlag())));
    }   
}// sSETNP_M

void BITBYTE::sSETZ_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isZeroFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_ZERO),
            ObjectSource(pTmgrTls->getTaintZeroFlag())));
    }   
}// sSETZ_M

void BITBYTE::sSETNZ_M(THREADID tid, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isParityFlagTainted())   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_ZERO),
            ObjectSource(pTmgrTls->getTaintParityFlag())));
    }   
}// sSETNZ_M

void BITBYTE::sSETBE_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr cfPtr = (pTmgrTls->isCarryFlagTainted()) 
        ? pTmgrTls->getTaintCarryFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!cfPtr && !zfPtr)   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objCarryFlag = ((bool) cfPtr) 
            ? ObjectSource(cfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, CARRY_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_BELOW_OR_EQUAL),
            objCarryFlag,
            objZeroFlag));
    }   
}// sSETBE_M

void BITBYTE::sSETNBE_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr cfPtr = (pTmgrTls->isCarryFlagTainted()) 
        ? pTmgrTls->getTaintCarryFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!cfPtr && !zfPtr)   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objCarryFlag = ((bool) cfPtr) 
            ? ObjectSource(cfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, CARRY_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_BELOW_OR_EQUAL),
            objCarryFlag,
            objZeroFlag));
    }   
}// sSETNBE_M

void BITBYTE::sSETL_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr)   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));

        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_LESS),
            objSignFlag,
            objOverflowFlag));
    }   
}// sSETL_M

void BITBYTE::sSETNL_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr)   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));

        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_LESS),
            objSignFlag,
            objOverflowFlag));
    }   
}// sSETNL_M

void BITBYTE::sSETLE_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;
    
    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr && !zfPtr)   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_LESS),
            objSignFlag,
            objOverflowFlag,
            objZeroFlag));
    }   
}// sSETLE_M

void BITBYTE::sSETNLE_M(THREADID tid, ADDRINT writeAddress, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;
    
    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr && !zfPtr)   pTmgrGlobal->unTaintMemory<8>(writeAddress);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_LESS),
            objSignFlag,
            objOverflowFlag,
            objZeroFlag));
    }   
}// sSETNLE_M


// --------------------
// DESTINATION REGISTRE
// --------------------


void BITBYTE::sSETB_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isCarryFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_BELOW),
            ObjectSource(pTmgrTls->getTaintCarryFlag())));
    }   
}// sSETB_R

void BITBYTE::sSETNB_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isCarryFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_BELOW),
            ObjectSource(pTmgrTls->getTaintCarryFlag())));
    }   
}// sSETNB_R

void BITBYTE::sSETS_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isSignFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_SIGN),
            ObjectSource(pTmgrTls->getTaintSignFlag())));
    }   
}// sSETS_R

void BITBYTE::sSETNS_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isSignFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_SIGN),
            ObjectSource(pTmgrTls->getTaintSignFlag())));
    }   
}// sSETS_R

void BITBYTE::sSETO_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isOverflowFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_OVERFLOW),
            ObjectSource(pTmgrTls->getTaintOverflowFlag())));
    }   
}// sSETO_R

void BITBYTE::sSETNO_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isOverflowFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_OVERFLOW),
            ObjectSource(pTmgrTls->getTaintOverflowFlag())));
    }   
}// sSETNO_R

void BITBYTE::sSETP_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isParityFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_PARITY),
            ObjectSource(pTmgrTls->getTaintParityFlag())));
    }   
}// sSETP_R

void BITBYTE::sSETNP_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isParityFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_PARITY),
            ObjectSource(pTmgrTls->getTaintParityFlag())));
    }   
}// sSETNP_R

void BITBYTE::sSETZ_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isZeroFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_ZERO),
            ObjectSource(pTmgrTls->getTaintZeroFlag())));
    }   
}// sSETZ_R

void BITBYTE::sSETNZ_R(THREADID tid, REG regDest, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // si flag non marqué, démarquage destination
    if (!pTmgrTls->isParityFlagTainted())   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_ZERO),
            ObjectSource(pTmgrTls->getTaintParityFlag())));
    }   
}// sSETNZ_R

void BITBYTE::sSETBE_R(THREADID tid, REG regDest, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr cfPtr = (pTmgrTls->isCarryFlagTainted()) 
        ? pTmgrTls->getTaintCarryFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!cfPtr && !zfPtr)   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objCarryFlag = ((bool) cfPtr) 
            ? ObjectSource(cfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, CARRY_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_BELOW_OR_EQUAL),
            objCarryFlag,
            objZeroFlag));
    }   
}// sSETBE_R

void BITBYTE::sSETNBE_R(THREADID tid, REG regDest, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr cfPtr = (pTmgrTls->isCarryFlagTainted()) 
        ? pTmgrTls->getTaintCarryFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!cfPtr && !zfPtr)   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objCarryFlag = ((bool) cfPtr) 
            ? ObjectSource(cfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, CARRY_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_BELOW_OR_EQUAL),
            objCarryFlag,
            objZeroFlag));
    }   
}// sSETNBE_R

void BITBYTE::sSETL_R(THREADID tid, REG regDest, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr)   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));

        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_LESS),
            objSignFlag,
            objOverflowFlag));
    }   
}// sSETL_R

void BITBYTE::sSETNL_R(THREADID tid, REG regDest, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;

    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr)   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));

        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_LESS),
            objSignFlag,
            objOverflowFlag));
    }   
}// sSETNL_R

void BITBYTE::sSETLE_R(THREADID tid, REG regDest, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;
    
    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr && !zfPtr)   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        _LOGTAINT(tid, insAddress, "SETLE_R");

        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_LESS_OR_EQUAL),
            objSignFlag,
            objOverflowFlag,
            objZeroFlag));
    }   
}// sSETLE_R

void BITBYTE::sSETNLE_R(THREADID tid, REG regDest, ADDRINT flagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    // récupération du marquage des flags avant l'exécution
    TaintBitPtr sfPtr = (pTmgrTls->isSignFlagTainted()) 
        ? pTmgrTls->getTaintSignFlag() 
        : nullptr;
    TaintBitPtr ofPtr = (pTmgrTls->isOverflowFlagTainted()) 
        ? pTmgrTls->getTaintOverflowFlag() 
        : nullptr;
    TaintBitPtr zfPtr = (pTmgrTls->isZeroFlagTainted()) 
        ? pTmgrTls->getTaintZeroFlag() 
        : nullptr;
    
    // si flags non marqués, démarquage destination
    if (!sfPtr && !ofPtr && !zfPtr)   pTmgrTls->unTaintRegister<8>(regDest);
    // sinon, création de l'objet et marquage destination
    else
    {    
        ObjectSource objSignFlag = ((bool) sfPtr) 
            ? ObjectSource(sfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, SIGN_FLAG));
        ObjectSource objOverflowFlag = ((bool) ofPtr) 
            ? ObjectSource(ofPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, OVERFLOW_FLAG));
        ObjectSource objZeroFlag = ((bool) zfPtr) 
            ? ObjectSource(zfPtr)
            : ObjectSource(1, EXTRACTBIT(flagsValue, ZERO_FLAG));

        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_SETCC,
            ObjectSource(32, PREDICATE_NOT_LESS_OR_EQUAL),
            objSignFlag,
            objOverflowFlag,
            objZeroFlag));
    }   
}// sSETNLE_R





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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
                IARG_INST_PTR, IARG_END);
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
            IARG_INST_PTR, IARG_END);
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
            IARG_INST_PTR, IARG_END);
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
            IARG_INST_PTR, IARG_END);
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
            IARG_INST_PTR, IARG_END);
    }
} // cBSF