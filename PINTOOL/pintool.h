#pragma once

// le kit 62376 de PIN provoque un warning de cast (C4244) à la compilation
#pragma warning( push )
#pragma warning( disable : 4244 )
#include "pin.h"
#pragma warning( pop )


#include <iostream> // std::cout pour erreurs d'initialisation principalement
#include <fstream>  // pour fichiers de log
#include <ctime>    // pour calcul du temps dans fichier de log

// Namespace obligatoire pour eviter les confilts WINAPI / PIN
namespace WINDOWS 
{
#include <windows.h>
}

// définitions des types de registres et des macros selon l'architecture 32/64 bits
#include <TaintEngine\architecture.h>

/* les types DWORD et HANDLE ne sont pas définis par PIN */
typedef unsigned long DWORD; 
typedef WINDOWS::HANDLE HANDLE;

/*********************/
/* Constantes utiles */
/*********************/

#define FUZZWIN_VERSION     "V0.5 26 avril 2014"

#define EXIT_EXCEPTION      -1 // exception trouvée (option checkscore)
#define EXIT_MAX_CONSTRAINTS 2 // fin du pintool pour cause de contrainte max
#define EXIT_TIMEOUT         3 // fin du pintool pour temps max dépassé

#define INIT_ERROR           0 // erreur d'initialisation
#define OPTION_TAINT         1 // pintool "fuzzwin"  : extraction contraintes marquées
#define OPTION_CHECKSCORE    2 // pintool checkscore : test et score de l'entrée

/*********************************************************/
/* Variables globales du programme (déclarations extern) */
/*********************************************************/

// handle du pipe de communication des resultats (tube nommé ou STDOUT avec l'option -nopipe)
extern HANDLE       g_hPipe;

// fichier d'entrée du programme fuzzé (passé via pipe ou ligne de commande)
extern std::string  g_inputFile; 
// option du pintool : taint ou ckeckscore
extern std::string  g_option;
// temps maximal d'execution
extern UINT32       g_maxTime;
// nombre maximal de contraintes
extern UINT32       g_maxConstraints;

// mode verbeux : logs de désassemblage et de marquage
extern bool          g_verbose;
extern std::ofstream g_debug;     // fichier de log du desassemblage
extern std::ofstream g_taint;     // fichier de log du marquage
extern clock_t       g_timeBegin; // chrono départ de l'instrumentation

// option pipe ou non pour l'échange du fichier initial  et de la formule finale
extern bool         g_nopipe;

// vrai dès que les premières données seront lues dans la source
extern bool         g_beginInstrumentationOfInstructions;

// clefs de stockage locales pour chaque thread

extern TLS_KEY      g_tlsKeyTaint;          // classe de marquage des registres
extern TLS_KEY      g_tlsKeySyscallData;    // stockage des données avant/apres syscall
extern TLS_KEY      g_tlsStringOpInfo;      // données statiques pour les instructions CMPS / SCAS

// structure de blocage inter-thread    
extern PIN_LOCK     g_lock;  

/** OPTION CHECKSCORE **/

// nombre de threads démarrés, et nombre de threads maxi supportés (10000)
extern UINT32         g_numThreads;
#define MaxNumThreads 10000

// vrai si erreur trouvée
extern bool        g_faultFound;

// nombre d'instructions exécutées par thread
// padding à 256 bits pour optimisation (cache)
class ThreadCount
{
public:
    UINT64 _count;
    UINT8 _pad[24]; 
}; 

extern ThreadCount g_icount[MaxNumThreads];

/** OPTIONS DE LA LIGNE DE COMMANDE **/

extern KNOB<std::string> KInputFile;     
extern KNOB<UINT32>      KMaxTime;
extern KNOB<std::string> KBytes;
extern KNOB<UINT32>      KMaxConstr;
extern KNOB<std::string> KOption;
extern KNOB<UINT32>      KOsType;
extern KNOB<BOOL>        KVerbose;
extern KNOB<BOOL>        KNoPipe;

/*******************************************************************/
/* procedure d'initialisation des variables globales et paramètres */
/*******************************************************************/
int pintoolInit(); // fichier initialize.cpp

/********************************/
/* MACROS DE LOG (mode verbose) */
/********************************/

// log de dessassemblage standard, partie instrumentation
inline void _LOGINSPROC(INS ins) 
{
    PIN_GetLock(&g_lock, PIN_ThreadId()); 
    g_debug << "[T:" << PIN_ThreadId() << "] " << hexstr(INS_Address(ins)); 
    g_debug << " " << INS_Disassemble(ins).c_str(); 
    PIN_ReleaseLock(&g_lock); 
}

#define _LOGINS(i)    if (g_verbose) _LOGINSPROC(i);

// log désassemblage, partie analyse
inline void _LOGDEBUGPROC(const std::string &s)
{
    PIN_GetLock(&g_lock, PIN_ThreadId()); 
    g_debug << s << std::endl; 
    PIN_ReleaseLock(&g_lock); 
}

#define _LOGDEBUG(s)  if (g_verbose) _LOGDEBUGPROC(s);

// log désassemblage, partie Syscalls uniquement 
inline void  _LOGSYSCALLSPROC(ADDRINT syscallNumber, const std::string &s)
{
    PIN_GetLock(&g_lock, PIN_ThreadId());      
    g_debug << "[T:"  << decstr(PIN_ThreadId());
    g_debug << "][P:" << hexstr(PIN_GetPid()); 
    g_debug << "][S:" << hexstr(syscallNumber);
    g_debug << s << std::endl; 
    PIN_ReleaseLock(&g_lock); 
}

#define _LOGSYSCALLS(sys, text) if (g_verbose) _LOGSYSCALLSPROC(sys, text);

inline void _LOGTAINTPROC(THREADID tid, ADDRINT insAddress, const std::string &s)
{
    PIN_GetLock(&g_lock, tid); 
    g_taint << "[T:"  << decstr(tid) << "] "; 
    g_taint << hexstr(insAddress) << " " << s << " MARQUE !! " << std::endl; 
    PIN_ReleaseLock(&g_lock); 
}

// log de marquage pour une instruction, avec adresse de l'instruction
#define _LOGTAINT(t, a, s)  if (g_verbose)  _LOGTAINTPROC(t, a, s);

/*****************************************/
/* classes globales de metaprogrammation */
/*****************************************/

// Renvoie le registre d'accumulation utilisé par certaines instructions
template<UINT32 lengthInBits> class RegisterACC 
{ public:  static inline REG getReg() { return REG_INVALID_ ; }};
template<> class RegisterACC<8> 
{ public:  static inline REG getReg() { return REG_AL; }};
template<> class RegisterACC<16> 
{ public:  static inline REG getReg() { return REG_AX; }};
template<> class RegisterACC<32>
{ public:  static inline REG getReg() { return REG_EAX; }};
#if TARGET_IA32E
template<> class RegisterACC<64> 
{ public:  static inline REG getReg() { return REG_RAX; }};
#endif

// Renvoie le registre I/O (AH/DX/EDX/RDX) utilisé par certaines instructions
template<UINT32 lengthInBits> class RegisterIO 
{ public:  static inline REG getReg() { return REG_INVALID_ ; }};
template<> class RegisterIO<8> 
{ public:  static inline REG getReg() { return REG_AH; }}; // 8 bits = AH et non DH (cf. instr MUL)
template<> class RegisterIO<16> 
{ public:  static inline REG getReg() { return REG_DX; }};
template<> class RegisterIO<32>
{ public:  static inline REG getReg() { return REG_EDX; }};
#if TARGET_IA32E
template<> class RegisterIO<64> 
{ public:  static inline REG getReg() { return REG_RDX; }};
#endif

// Renvoie le registre compteur (CX/ECX/RCX) utilisé pour JRCXZ
template<UINT32 lengthInBits> class RegisterCount 
{ 
public:  
    static inline REG getReg()             { return REG_INVALID_ ; }
    static inline PREDICATE getPredicate() { return PREDICATE_ALWAYS_TRUE ; }
};

template<> class RegisterCount<16> 
{ 
public:  
    static inline REG getReg()             { return REG_CX ; }
    static inline PREDICATE getPredicate() { return PREDICATE_CX_NON_ZERO ; }
};

template<> class RegisterCount<32>
{ 
public:  
    static inline REG getReg()             { return REG_ECX ; }
    static inline PREDICATE getPredicate() { return PREDICATE_ECX_NON_ZERO ; }
};

#if TARGET_IA32E
template<> class RegisterCount<64> 
{ 
public:  
    static inline REG getReg()             { return REG_RCX ; }
    static inline PREDICATE getPredicate() { return PREDICATE_RCX_NON_ZERO ; }
};
#endif

// détermination de la valeur "ff" en fonction de la taille fournie (en bits)
// utilisé par les fonctions d'analyse traitant les instructions LOGICAL::OR et STRINGOP::SCAS
// constantes définies dans <limits.h>
template<UINT32 lengthInBits> class ValueFF
{ public:  static inline const ADDRINT get() { return NULL; }};
template<> class ValueFF<8>
{ public:  static inline const ADDRINT get() { return (_UI8_MAX); }};
template<> class ValueFF<16>
{ public:  static inline const ADDRINT get() { return (_UI16_MAX); }};
template<> class ValueFF<32>
{ public:  static inline const ADDRINT get() { return (_UI32_MAX); }};
#if TARGET_IA32E
template<> class ValueFF<64>
{ public:  static inline const ADDRINT get() { return (_UI64_MAX); }};
#endif

