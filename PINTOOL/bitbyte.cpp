#include "bitbyte.h"
#include "buildFormula.h"
#include "utils.h"  // démarquage suite à SETcc

/*************/
/*** SETcc ***/
/*************/

//! tous les callbacks pour SETcc suivent le même principe 
//! SETcc ne fait pas partie des instructions avec prédicats 
//! qui utilisent le paramètre IARG_EXECUTING (comme CMOVcc et Jcc)
//! Dans la conception de PIN, l'instruction est en effet toujours exécutée : elle
//! fixe la destination (registre ou mémoire, 8 bits) à 0 ou 1 selon la valeur du prédicat
//! 
//! Deux cas seront distingués:
//!
//! *-> cas REGISTRE : instrumentation en IPOINT_AFTER
//! avec passage en arguments de la destination (et des flags selon le type de predicat)
//! la fonction d'analyse lit la valeur du registre après exécution
//! s'il vaut 1, le predicat était vrai => ajout de la contrainte correspondante
//! et démarquage du registre
//!
//! *-> cas MEMOIRE : instrumentation en IF(BEFORE)/THEN(AFTER)
//! en effet impossible d'obtenir l'argument mémoire en IPOINT_AFTER
//! donc en InsertIfCall(Before), on passe comme arguement l'adresse qui sera modifiée
//! la fonction d'analyse 'Before' démarque la mémoire (quoi qu'il arrive elle sera démarquée)
//! et vérifie le marquage du flag concerné.
//! Si marqué, enregistrement de l'adresse de destination en variable globale
//! et retour de la valeur 'True' pour déclencher l'instrumentation 'Then'
//!
//! l'instrumentation 'then' a comme argument la valeur des flags selon le type de predicat
//! la fonction d'analyse lit la valeur de la mémoire après exécution
//! s'il vaut 1, le predicat était vrai => ajout de la contrainte correspondante

// adresse d'écriture d'une instruction SETCC_M
static ADDRINT g_writeAddressSetcc;

void BITBYTE::cSETB(INS &ins) 
{ 
    // SETB/SETNAE/SETC   CF = 1          Below/not above or equal/carry     
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETB_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETB_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETB_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETB

void BITBYTE::cSETNB(INS &ins) 
{ 
    // SETAE/SETNB/SETNC  CF = 0     Above or equal/not below
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETB
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETB_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNB_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNB_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNB

void BITBYTE::cSETS(INS &ins) 
{ 
    // SETS           SF = 1          Sign (negative)   
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETS_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETS_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETS_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETS

void BITBYTE::cSETNS(INS &ins) 
{
    // SETNS          SF = 0          Not sign (non-negative) 
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETS
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETS_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNS_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNS_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNS

void BITBYTE::cSETO(INS &ins) 
{ 
    // SETO           OF = 1          Overflow  
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETO_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETO_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETO_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETO

void BITBYTE::cSETNO(INS &ins) 
{
    // SETNO          OF = 0          Not overflow   
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETO
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETO_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNO_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNO_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETNO

void BITBYTE::cSETP(INS &ins) 
{
    // SETP/SETPE       PF = 1          Parity/parity even 
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETP_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETP_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETP_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETP
       
void BITBYTE::cSETNP(INS &ins) 
{
    // SETNP/SETPO      PF = 0          Not parity/parity odd 
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETP
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETP_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNP_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNP_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNP

void BITBYTE::cSETZ(INS &ins) 
{ 
    // SETE/SETZ        ZF = 1          Equal/zero
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETZ_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETZ_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETZ_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETZ

void BITBYTE::cSETNZ(INS &ins) 
{
    // SETNE/SETNZ      ZF = 0          Not equal/not zero
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETZ
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETZ_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNZ_M_AFTER,         
            IARG_THREAD_ID,
            IARG_INST_PTR,    // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNZ_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    }
}// cSETNZ

void BITBYTE::cSETBE(INS &ins) 
{ 
    // SETBE/SETNA      (CF or ZF) = 1  Below or equal/not above  
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETBE_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETBE_M_AFTER,         
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,              // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETBE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
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
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETBE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETBE_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNBE_M_AFTER,         
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,              // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNBE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
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
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETL_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETL_M_AFTER,         
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,              // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETL_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
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
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETL
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETL_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNL_M_AFTER,         
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,              // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNL_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
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
        // Instrumentation 'If' en IPOINT_BEFORE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETLE_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETLE_M_AFTER,         
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,              // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETLE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETLE

void BITBYTE::cSETNLE(INS &ins) 
{
    if (INS_IsMemoryWrite(ins))     
    {   
        // Instrumentation 'If' en IPOINT_BEFORE : idem SETLE
        INS_InsertIfCall (ins, IPOINT_BEFORE, (AFUNPTR) sSETLE_M_BEFORE,         
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,    // adresse de destination (8 bits)
            IARG_END);

        // Instrumentation 'Then' en IPOINT_AFTER
        INS_InsertThenCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNLE_M_AFTER,         
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,              // adresse de l'instruction
            IARG_END);
    }
    else // forcement registre
    {
        REG regDest = INS_RegW(ins, 0);  // registre de destination (8 bits) qui sera démarqué
        INS_InsertCall (ins, IPOINT_AFTER, (AFUNPTR) sSETNLE_R,         
            IARG_THREAD_ID,
            IARG_UINT32, regDest,    // registre de destination (8 bits) qui sera démarqué
            IARG_REG_VALUE, regDest, // sa valeur (qui sera 0 ou 1 selon valeur prédicat)
            IARG_REG_VALUE, REG_GFLAGS, // valeur exacte des flags
            IARG_INST_PTR,          // adresse de l'instruction
            IARG_END);
    } 
}// cSETNLE

/*******************/
/****  SIMULATE ****/
/*******************/

#if 0

// -----------------------------------------------
// destination mémoire : partie IF (IPOINT_BEFORE)
// -----------------------------------------------

ADDRINT BITBYTE::sSETB_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETB_M_BEFORE

ADDRINT BITBYTE::sSETS_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{ 
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isSignFlagTainted()) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETS

ADDRINT BITBYTE::sSETO_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isOverflowFlagTainted()) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETO

ADDRINT BITBYTE::sSETP_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{ 
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isParityFlagTainted()) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETP

ADDRINT BITBYTE::sSETZ_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{ 
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isZeroFlagTainted()) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETZ

ADDRINT BITBYTE::sSETBE_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isZeroFlagTainted() || pTmgrTls->isCarryFlagTainted() ) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETBE

ADDRINT BITBYTE::sSETL_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isSignFlagTainted() || pTmgrTls->isOverflowFlagTainted() ) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETL

ADDRINT BITBYTE::sSETLE_M_BEFORE(THREADID tid, ADDRINT writeAddress)
{ 
    TaintManager_Thread* pTmgrTls    = getTmgrInTls(tid);
    ADDRINT              returnValue = 0;    // par défaut pas d'instrumentation 'Then'
   
    // démarquage de la destination quoi qu'il arrive
    pTmgrGlobal->unTaintMemory<8>(writeAddress);
    
    // si flag marqué, traitement de la contrainte dans la partie 'then' (retour non nul)   
    if (pTmgrTls->isZeroFlagTainted() 
        || pTmgrTls->isSignFlagTainted() 
        || pTmgrTls->isOverflowFlagTainted() ) 
    {
        // stockage adresse de destination pour traitement dans la partie 'then'
        g_writeAddressSetcc = writeAddress;
        returnValue         = 1;
    }   
    return (returnValue);
}// sSETLE

// ------------------------------------------------
// destination mémoire : partie THEN (IPOINT_AFTER)
// ------------------------------------------------

void BITBYTE::sSETB_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETB_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0));
    PIN_ReleaseLock(&g_lock);

}// sSETB_M_AFTER

void BITBYTE::sSETNB_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNB_M_AFTER");

    // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0));
    PIN_ReleaseLock(&g_lock);

}// sSETNB_M_AFTER

void BITBYTE::sSETS_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETS_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_SIGN(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0));
    PIN_ReleaseLock(&g_lock);

}// sSETS_M_AFTER

void BITBYTE::sSETNS_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNS_M_AFTER");

    // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_SIGN(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0));
    PIN_ReleaseLock(&g_lock);

}// sSETNS_M_AFTER

void BITBYTE::sSETO_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETO_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0));
    PIN_ReleaseLock(&g_lock);

}// sSETO_M_AFTER

void BITBYTE::sSETNO_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNO_M_AFTER");

    // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_OVERFLOW(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0));
    PIN_ReleaseLock(&g_lock);

}// sSETNO_M_AFTER

void BITBYTE::sSETP_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETB_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_PARITY(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0));
    PIN_ReleaseLock(&g_lock);

}// sSETP_M_AFTER

void BITBYTE::sSETNP_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNP_M_AFTER");

    // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_PARITY(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0));
    PIN_ReleaseLock(&g_lock);

}// sSETNP_M_AFTER

void BITBYTE::sSETZ_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETZ_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_ZERO(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0));
    PIN_ReleaseLock(&g_lock);

}// sSETZ_M_AFTER

void BITBYTE::sSETNZ_M_AFTER(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNZ_M_AFTER");

    // prédicat vrai si la destination est non nulle + inversion car NOT BELOW
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_ZERO(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0));
    PIN_ReleaseLock(&g_lock);

}// sSETNZ_M_AFTER

void BITBYTE::sSETBE_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETBE_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0), eflagsValue);
    PIN_ReleaseLock(&g_lock);

}// sSETBE_M_AFTER

void BITBYTE::sSETNBE_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNBE_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_BELOW_OR_EQUAL(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0), eflagsValue);
    PIN_ReleaseLock(&g_lock);

}// sSETNBE_M_AFTER

void BITBYTE::sSETL_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETL_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_LESS(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0), eflagsValue);
    PIN_ReleaseLock(&g_lock);

}// sSETL_M_AFTER

void BITBYTE::sSETNL_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNL_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_LESS(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0), eflagsValue);
    PIN_ReleaseLock(&g_lock);

}// sSETNL_M_AFTER

void BITBYTE::sSETLE_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETLE_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) != 0), eflagsValue);
    PIN_ReleaseLock(&g_lock);

}// sSETLE_M_AFTER

void BITBYTE::sSETNLE_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    _LOGTAINT("SETNLE_M_AFTER");

    // prédicat vrai si la destination est non nulle
    PIN_GetLock(&g_lock, 0);
    g_pFormula->addConstraint_LESS_OR_EQUAL(pTmgrTls, insAddress,
        (getMemoryValue<8>(g_writeAddressSetcc) == 0), eflagsValue);
    PIN_ReleaseLock(&g_lock);

}// sSETNLE_M_AFTER

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

#endif


ADDRINT BITBYTE::sSETB_M_BEFORE  (THREADID tid, ADDRINT writeAddress){ return 0;}
ADDRINT BITBYTE::sSETS_M_BEFORE  (THREADID tid, ADDRINT writeAddress){return 0;}
ADDRINT BITBYTE::sSETO_M_BEFORE  (THREADID tid, ADDRINT writeAddress){return 0;}
ADDRINT BITBYTE::sSETP_M_BEFORE  (THREADID tid, ADDRINT writeAddress){return 0;}
ADDRINT BITBYTE::sSETZ_M_BEFORE  (THREADID tid, ADDRINT writeAddress){return 0;}
ADDRINT BITBYTE::sSETBE_M_BEFORE (THREADID tid, ADDRINT writeAddress){return 0;}
ADDRINT BITBYTE::sSETL_M_BEFORE  (THREADID tid, ADDRINT writeAddress){return 0;}
ADDRINT BITBYTE::sSETLE_M_BEFORE (THREADID tid, ADDRINT writeAddress){return 0;}
// Partie THEN (IPOINT_AFTER)
void BITBYTE::sSETB_M_AFTER  (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETNB_M_AFTER (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETS_M_AFTER  (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETNS_M_AFTER (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETO_M_AFTER  (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETNO_M_AFTER (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETP_M_AFTER  (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETNP_M_AFTER (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETZ_M_AFTER  (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETNZ_M_AFTER (THREADID tid, ADDRINT insAddress){}
void BITBYTE::sSETBE_M_AFTER (THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETNBE_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETL_M_AFTER  (THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETNL_M_AFTER (THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETLE_M_AFTER (THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETNLE_M_AFTER(THREADID tid, ADDRINT eflagsValue, ADDRINT insAddress){}

// destination registre
void BITBYTE::sSETB_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETNB_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETS_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETNS_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETO_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETNO_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETP_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETNP_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETZ_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETNZ_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT insAddress){}
void BITBYTE::sSETBE_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETNBE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETL_R  (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETNL_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETLE_R (THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress){}
void BITBYTE::sSETNLE_R(THREADID tid, REG regDest, ADDRINT regDestValue, ADDRINT eflagsValue, ADDRINT insAddress){}




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