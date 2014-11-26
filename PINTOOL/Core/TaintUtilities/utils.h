#pragma once 
#include <TaintEngine\TaintManager.h>

// Macros composant les arguments utilisés lors de l'insertion d'une fonction d'analyse 
// pour construire un objet représentant l'adressage indirect d'une opérande mémoire 
// ces arguments seront ajoutés à une IARGLIST
// NB : dans tous les cas, le premier arguement de IARGLIST sera le THREADID
 
#define IARGLIST_BISD IARG_UINT32,    baseReg,  /* registre de base utilisé */ \
                      IARG_REG_VALUE, baseReg,  /* valeur lors du callback  */ \
                      IARG_UINT32,    indexReg, /* registre d'index utilisé */ \
                      IARG_REG_VALUE, indexReg, /* valeur lors du callback  */ \
                      IARG_UINT32,    scale,    /* valeur du scale          */ \
                      IARG_UINT32,    displ     /* déplacement (ici casté)  */ 
#define FUNCARGS_BISD THREADID tid,                        \
                      REG baseReg,  ADDRINT baseRegValue,  \
                      REG indexReg, ADDRINT indexRegValue, \
                      UINT32 scale,                        \
                      INT32 displ                          \
                     , ADDRINT insAddress

#define IARGLIST_BIS  IARG_UINT32,    baseReg,  /* registre de base utilisé */ \
                      IARG_REG_VALUE, baseReg,  /* valeur lors du callback  */ \
                      IARG_UINT32,    indexReg, /* registre d'index utilisé */ \
                      IARG_REG_VALUE, indexReg, /* valeur lors du callback  */ \
                      IARG_UINT32,    scale     /* valeur du scale */
#define FUNCARGS_BIS  THREADID tid,                        \
                      REG baseReg,  ADDRINT baseRegValue,  \
                      REG indexReg, ADDRINT indexRegValue, \
                      UINT32 scale                         \
                     , ADDRINT insAddress

#define IARGLIST_BID  IARG_UINT32,    baseReg, /* registre de base utilisé*/ \
                      IARG_REG_VALUE, baseReg, /* valeur lors du callback */ \
                      IARG_UINT32,    indexReg,/* registre d'index utilisé*/ \
                      IARG_REG_VALUE, indexReg, /* valeur lors du callback*/ \
                      IARG_UINT32,    displ     /* déplacement (ici casté)*/ 
#define FUNCARGS_BID  THREADID tid,                        \
                      REG baseReg,  ADDRINT baseRegValue,  \
                      REG indexReg, ADDRINT indexRegValue, \
                      INT32 displ                          \
                     , ADDRINT insAddress

#define IARGLIST_BI   IARG_UINT32,    baseReg, /* registre de base utilisé*/ \
                      IARG_REG_VALUE, baseReg, /* valeur lors du callback */ \
                      IARG_UINT32,    indexReg,/* registre d'index utilisé*/ \
                      IARG_REG_VALUE, indexReg  /* valeur lors du callback*/ 
#define FUNCARGS_BI   THREADID tid,                        \
                      REG baseReg,  ADDRINT baseRegValue,  \
                      REG indexReg, ADDRINT indexRegValue  \
                     , ADDRINT insAddress

#define IARGLIST_BD   IARG_UINT32,    baseReg, /* registre de base utilisé */\
                      IARG_REG_VALUE, baseReg, /* valeur lors du callback */ \
                      IARG_UINT32,    displ    /* déplacement (ici casté)*/ 
#define FUNCARGS_BD   THREADID tid,                        \
                      REG baseReg,  ADDRINT baseRegValue,  \
                      INT32 displ                          \
                     , ADDRINT insAddress

#define IARGLIST_B    IARG_UINT32,    baseReg, /* registre de base utilisé */\
                      IARG_REG_VALUE, baseReg  /* valeur lors du callback */ 
#define FUNCARGS_B    THREADID tid,                        \
                      REG baseReg,  ADDRINT baseRegValue   \
                     , ADDRINT insAddress

#define IARGLIST_ISD  IARG_UINT32,    indexReg,/* registre d'index utilisé*/ \
                      IARG_REG_VALUE, indexReg, /* valeur lors du callback*/ \
                      IARG_UINT32,    scale,    /* valeur du scale        */ \
                      IARG_UINT32,    displ     /* déplacement (ici casté)*/
#define FUNCARGS_ISD  THREADID tid,                        \
                      REG indexReg, ADDRINT indexRegValue, \
                      UINT32 scale,                        \
                      INT32 displ                          \
                     , ADDRINT insAddress

#define IARGLIST_IS   IARG_UINT32,    indexReg,/* registre d'index utilisé*/ \
                      IARG_REG_VALUE, indexReg, /* valeur lors du callback*/ \
                      IARG_UINT32,    scale     /* valeur du scale        */
#define FUNCARGS_IS   THREADID tid,                        \
                      REG indexReg, ADDRINT indexRegValue, \
                      UINT32 scale                         \
                     , ADDRINT insAddress

// Macro de construction d'une liste d'arguments
#define _MAKE_ARGS_EA(x)   callback = (AFUNPTR) UTILS::computeEA_##x##; \
                           IARGLIST_AddArguments(args, IARG_THREAD_ID,  \
                           IARGLIST_##x##, IARG_INST_PTR, IARG_END); 


namespace UTILS 
{

void cUNHANDLED(INS &ins);

void cGetKindOfEA(const INS &ins);


template<UINT32 len> 
void PIN_FAST_ANALYSIS_CALL uREG  (THREADID tid, REG reg);
void PIN_FAST_ANALYSIS_CALL uMEM  (ADDRINT address, UINT32 sizeInBytes);
void PIN_FAST_ANALYSIS_CALL uFLAGS(THREADID tid);

// calcule et stocke un objet correspondant au marquage de l'adresse indirecte
// l'adresse est calculée sur 32bits (x86) ou 64bits (x64) et stockée dans TaintManager
// l'appelant pourra alors l'adapter à la longueur réelle de l'adresse effective (OperandSize)

void computeEA_BISD(FUNCARGS_BISD);
void computeEA_BIS (FUNCARGS_BIS);
void computeEA_BID (FUNCARGS_BID);
void computeEA_BI  (FUNCARGS_BI);
void computeEA_BD  (FUNCARGS_BD);
void computeEA_B   (FUNCARGS_B);
void computeEA_ISD (FUNCARGS_ISD);
void computeEA_IS  (FUNCARGS_IS);
} // namespace UTILS

#include "utils.hpp"
