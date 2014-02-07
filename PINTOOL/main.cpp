/*BEGIN_LEGAL 
Intel Open Source License 

Copyright (c) 2002-2013 Intel Corporation. All rights reserved.
 
Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.  Redistributions
in binary form must reproduce the above copyright notice, this list of
conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.  Neither the name of
the Intel Corporation nor the names of its contributors may be used to
endorse or promote products derived from this software without
specific prior written permission.
 
THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE INTEL OR
ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
END_LEGAL */

#include "instrumentation.h"
#include "pintool.h"
#include "syscalls.h"
#include "TaintManager.h"
#include "buildFormula.h"

#include <locale> // pour prise en compte des paramètres régionaux locaux

/* ================================================================== */
// Doxygen MainPage
/* ================================================================== */

//! \mainpage Page d'accueil
//! \section intro Introduction
//!
//! Ceci est l'introduction

/* ================================================================== */
// Global variables
/* ================================================================== */

TaintManager_Global *pTmgrGlobal;
SolverFormula       *pFormula;

TLS_KEY             tlsKeyTaint;
TLS_KEY             tlsKeySyscallData;

PIN_LOCK            lock;      // structures de blocage inter-thread

std::string         inputFile; // fichier d'entrée pour le programme fuzzé
WINDOWS::HANDLE     hPipe;     // handle du pipe de communication (ou STDOUT en mode DEBUG)

bool    beginInstrumentation; // VRAI lorque les premiers octets auront été lus dans le fichier cible
UINT32  maxConstraints;
UINT32  maxTime;

//bool isInsideRoutine      = false;

#if DEBUG
ofstream    debug;
ofstream    taint;
clock_t     timeBegin;
UINT64      nbIns;
#endif

/* ===================================================================== */
// Command line switches
/* ===================================================================== */

#if DEBUG
KNOB<string> KnobInputFile(KNOB_MODE_WRITEONCE, "pintool", "i", "", "fichier d'entree");
KNOB<UINT32> KnobMaxExecutionTime(KNOB_MODE_WRITEONCE, "pintool", "m", "0", "temps maximal d'execution");
KNOB<string> KnobBytesToTaint(KNOB_MODE_WRITEONCE, "pintool", "b", "all", "intervelles d'octets à surveiller");
KNOB<UINT32> KnobMaxConstraints(KNOB_MODE_WRITEONCE, "pintool", "c", "0", "nombre maximal de contraintes");
#endif

/* ===================================================================== */
// Main procedure
/* ===================================================================== */

int main(int argc, char *argv[]) 
{
    // Initialisation du traitement des symboles (pour les routines)
    //PIN_InitSymbols();
   
    // Initialisation de PIN. Renvoie TRUE si erreur trouvée
    if (PIN_Init(argc, argv)) PIN_ExitProcess(-1); 

    // initialisation des arguments (différents selon debug ou release)
    // en mode debug, il ne faut pas d'accents dans le nom du fichier étudié passé via la ligne de comande
    if (!fuzzwinInit()) PIN_ExitProcess(-2);

    // fonctions d'instrumentation des appels systèmes
    PIN_AddSyscallEntryFunction(SYSCALLS::syscallEntry, 0);
    PIN_AddSyscallExitFunction(SYSCALLS::syscallExit, 0);

    // fonction d'instrumentation de chaque instruction
    INS_AddInstrumentFunction(INSTRUMENTATION::Instruction, 0);
    
    // fonction d'instrumentation du chargement des images (DLL) 
    // IMG_AddInstrumentFunction(INSTRUMENTATION::Image, 0);

    // fonction d'instrumentation des routines (pour tester exploit retour)
    // RTN_AddInstrumentFunction(INSTRUMENTATION::Routine, 0);
    
    // Fonction appelée lors de la fin du programme
    // version spécifique pour le multithreading
    PIN_AddFiniUnlockedFunction(INSTRUMENTATION::Fini, 0);

    // Fonctions de notification de la creation et de la
    // suppression des threads de l'application
    PIN_AddThreadStartFunction(INSTRUMENTATION::threadStart, 0);
    PIN_AddThreadFiniFunction (INSTRUMENTATION::threadFini, 0);

    // Démarrage de l'instrumentation, ne retourne jamais
    PIN_StartProgram();

    return 1; // valeur "normale" (timeout non dépassé)
}

/* ===================================================================== */
/* eof */
/* ===================================================================== */
