/*!

 * \file fuzzwin.h
 * \brief header général pour le pintool 
 * \author Sébastien LECOMTE
 * \version 05.a
 * \date 30/07/2013

 * contient les définitions générales utilisées par tous
 * les fichiers source du projet
*/

#pragma once

// le kit 62376 de PIN provoque un warning de cast (C4244) à la compilation
// on désactive donc ce warning ici
#pragma warning( push )
#pragma warning( disable : 4244 ) // cast de ADDRINT en UINT32 dans REGSET.PH
#include "pin.h"
#pragma warning( pop )

#include "architecture.h"
#include <string>
#include <iostream> // std::cout

/// Namespace obligatoire pour eviter les confilts avec PIN
namespace WINDOWS  
{
    #include <windows.h>
}

typedef unsigned long DWORD; // le type DWORD n'est pas défini par PIN

/***********************************/
/* Variables globales du programme */
/***********************************/

// handle du pipe de communication des resultats (STDOUT en DEBUG, pipe avec SAGE en RELEASE)
extern WINDOWS::HANDLE hPipe;

// fichier d'entrée du programme fuzzé
extern std::string inputFile; 

// nombre maximal de contraintes
extern UINT32 maxConstraints;
// temps maximal d'execution
extern UINT32 maxTime;

// vrai dès que les premières données seront lues dans la source
extern bool beginInstrumentation;

// vrai si l'instruction ou le syscall étudié est au sein d'une routine suivie (_read, ...)
// auquel cas il n'y aura pas d'instrumentation
// extern bool isInsideRoutine;

// clefs de stockage locales pour chaque thread
extern TLS_KEY tlsKeyTaint; 
extern TLS_KEY tlsKeySyscallData;

// structure de blocage inter-thread    
extern PIN_LOCK lock;     

/*******************************************************************/
/* procedure d'initialisation des variables globales et paramètres */
/*******************************************************************/
int fuzzwinInit();

/****************************************************/
/* variables et fonctions spécifiques au mode DEBUG */
/****************************************************/

#if DEBUG // mode DEBUG

#include <fstream>
#include <ctime> // pour log

extern UINT64 nbIns; // nb d'instructions non gérées
extern clock_t timeBegin;

extern KNOB<string> KnobInputFile;
extern KNOB<UINT32> KnobMaxExecutionTime;
extern KNOB<string> KnobBytesToTaint;
extern KNOB<UINT32> KnobMaxConstraints;

extern std::ofstream debug; // fichier de log du desassemblage
extern std::ofstream taint; // fichier de log du marquage

// log de marquage pour une instruction
#define _LOGTAINT(t)     { \
    PIN_GetLock(&lock, PIN_ThreadId()); \
    taint << std::hex << insAddress << std::dec << " " << t << " MARQUE !! " << std::endl; \
    PIN_ReleaseLock(&lock); }

// log de dessassemblage standard (partie instrumentation)
#define _LOGINS(ins)  { \
    PIN_GetLock(&lock, PIN_ThreadId()); \
    debug << "[T:" << PIN_ThreadId() << "] 0x" << std::hex << INS_Address(ins); \
    debug << " " << INS_Disassemble(ins).c_str(); \
    PIN_ReleaseLock(&lock); }

// log désassemblage, partie analyse
#define _LOGDEBUG(s)  { \
    PIN_GetLock(&lock, PIN_ThreadId()); \
    debug << s << std::endl; \
    PIN_ReleaseLock(&lock); }

// log désassemblage, partie Syscalls
#define _LOGSYSCALLS(s)  { \
    PIN_GetLock(&lock, PIN_ThreadId());      \
    debug << "[T:"  << decstr(tid);          \
    debug << "][P:" << hexstr(PIN_GetPid()); \
    debug << "][S:" << hexstr(syscallNumber);\
    debug << s << std::endl; \
    PIN_ReleaseLock(&lock); }

// log de dessasemblage suite à non prise en charge d'une instruction
#define _LOGUNHANDLED(ins)  { \
    PIN_GetLock(&lock, PIN_ThreadId()); \
    debug << " *** non instrumenté ***"; \
    PIN_ReleaseLock(&lock); }

// argument pour l'enregistrement d'un callback : adresse de l'instruction
#define CALLBACK_DEBUG  IARG_INST_PTR,  

// argument correspondant à l'adresse de l'instruction
#define ADDRESS_DEBUG   ,ADDRINT insAddress 

// argument ajouté lors de l'appel à une fonction hors du cas callback
#define INSADDRESS      ,insAddress

#else // Mode RELEASE : aucune fonction

#define ADDRESS_DEBUG   
#define CALLBACK_DEBUG 
#define INSADDRESS
#define _LOGTAINT(t)
#define _LOGINS(ins)
#define _LOGUNHANDLED(ins)
#define _LOGDEBUG(s)
#define _LOGSYSCALLS(s)
#endif