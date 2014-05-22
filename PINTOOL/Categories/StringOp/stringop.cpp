#include "stringop.h"
#include <Dataxfer\dataxfer.h>	// pour STOS et LODS 
#include <Binary\binary.h>		// pour SCAS sans préfixe REP
#include <Translate\translate.h>

// pour les instructions MOVS, LODS et STOS, 
// un seul prefixe possible : REP, avec (e/r)cx comme compteur
// ASTUCE : faire un insert IF/PredicatedTHEN, avec 
//	 en IF : fonction "returnArg" retournant si c'est la 1ere itération ou pas
//	 en PredicatedThen : le callback avec nombre de répétitions en argument
//   (NB: le "Predicated" evite d'appeler la fonction si RCX est nul)
// ainsi, dans le cas d'une boucle de 45 itérations, il y aura 45 "returnArg"
// et une seule à la fonction de callback => optimisation !! 
// (cf /source/tools/ManualExamples/countreps.cpp)

ADDRINT PIN_FAST_ANALYSIS_CALL STRINGOP::returnArg(BOOL arg)
{ return arg; }

//////////
// MOVS //
//////////
// CALLBACKS
void STRINGOP::cMOVS(INS &ins, UINT32 size)
{ 
    void (*callback)() = nullptr;
    switch (size) 
    {	// taille de l'opérande mémoire de destination
    case 1:	callback = (AFUNPTR) sMOVS<8>;	break;
    case 2:	callback = (AFUNPTR) sMOVS<16>;	break;
    case 4:	callback = (AFUNPTR) sMOVS<32>;	break;
    #if TARGET_IA32E
    case 8: callback = (AFUNPTR) sMOVS<64>;	break;
    #endif
    }
    
    if (INS_HasRealRep(ins)) // instruction préfixée par REP
    {	
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR) returnArg, 
            IARG_FAST_ANALYSIS_CALL,
            IARG_FIRST_REP_ITERATION, IARG_END);
        INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, callback,
            IARG_REG_VALUE, INS_RepCountRegister(ins),	// nombre de repets	
            IARG_REG_VALUE,	REG_GFLAGS,	// pour direction flag: DF
            IARG_MEMORYREAD_EA,			// Adresse de lecture initiale
            IARG_MEMORYWRITE_EA,		// adresse d'ecriture initiale
            IARG_INST_PTR, IARG_END);
    }
    else 	// pas de préfixe REP : une seule répétition
    {	
        INS_InsertCall(ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_ADDRINT, 1,	// 1 repetition
            IARG_ADDRINT,	0,	// valeur des flags : peu importe
            IARG_MEMORYREAD_EA,	// Adresse de lecture initiale
            IARG_MEMORYWRITE_EA,// adresse d'ecriture initiale
            IARG_INST_PTR, IARG_END);
    }
} // cMOVS


//////////
// LODS //
//////////
void STRINGOP::cLODS(INS &ins, UINT32 size)
{ 
    void (*callback)() = nullptr;
    if (INS_HasRealRep(ins)) 	// instruction préfixée par REP
    {	
        switch (size) 	// taille de l'opérande mémoire de destination
        {
        case 1:	callback = (AFUNPTR) sLODS<8>;	break;
        case 2:	callback = (AFUNPTR) sLODS<16>;	break;
        case 4:	callback = (AFUNPTR) sLODS<32>;	break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sLODS<64>;	break;
        #endif
        }
        
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR) returnArg, 
            IARG_FAST_ANALYSIS_CALL,
            IARG_FIRST_REP_ITERATION, 
            IARG_END);
        INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_REG_VALUE, INS_RepCountRegister(ins),	// nombre de repets
            IARG_REG_VALUE,	REG_GFLAGS,	// valeur des flags (DF)
            IARG_MEMORYREAD_EA,			// Adresse de lecture initiale
            IARG_INST_PTR, IARG_END);
    }
    else // pas de préfixe : une seule répét, <=> mov AL/AX/EAX/EAX, [ESI]
    {	
        REG regDest = REG_INVALID();	// registre de destination
        switch (size) 	// taille de l'opérande mémoire source
        {
        case 1:	callback = (AFUNPTR) DATAXFER::sMOV_MR<8>;	regDest = REG_AL;	break;
        case 2:	callback = (AFUNPTR) DATAXFER::sMOV_MR<16>;	regDest = REG_AX;	break;
        case 4:	callback = (AFUNPTR) DATAXFER::sMOV_MR<32>;	regDest = REG_EAX;	break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) DATAXFER::sMOV_MR<64>;	regDest = REG_RAX;	break;
        #endif
        }
        
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,		// adresse réelle de lecture
            IARG_UINT32, regDest,   // registre destination
            IARG_INST_PTR, IARG_END);
    }
} // cLODS

//////////
// STOS //
//////////
// CALLBACKS
void STRINGOP::cSTOS(INS &ins, UINT32 size)
{ 
    void (*callback)() = nullptr;
    if (INS_HasRealRep(ins)) 	// instruction préfixée par REP
    {	
        switch (size) 	// taille de l'opérande mémoire de destination
        {
        case 1:	callback = (AFUNPTR) sSTOS<8>;	break;
        case 2:	callback = (AFUNPTR) sSTOS<16>;	break;
        case 4:	callback = (AFUNPTR) sSTOS<32>;	break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sSTOS<64>;	break;
        #endif
        }
        
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR) STRINGOP::returnArg, 
            IARG_FAST_ANALYSIS_CALL,
            IARG_FIRST_REP_ITERATION, 
            IARG_END);
        INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_REG_VALUE, INS_RepCountRegister(ins),	// nombre de repets
            IARG_REG_VALUE,	REG_GFLAGS,	// valeur des flags (DF)
            IARG_MEMORYWRITE_EA,		// Adresse d'écriture initiale
            IARG_INST_PTR, IARG_END);
    }
    else // pas de préfixe REP : équivalent à mov [ESI], AL/AX/EAX/EAX
    {	
        REG regSrc = REG_INVALID();	// registre source
        switch (size) 	// taille de l'opérande mémoire source
        {
        case 1:	callback = (AFUNPTR) DATAXFER::sMOV_RM<8>;	regSrc = REG_AL;  break;
        case 2:	callback = (AFUNPTR) DATAXFER::sMOV_RM<16>;	regSrc = REG_AX;  break;
        case 4:	callback = (AFUNPTR) DATAXFER::sMOV_RM<32>;	regSrc = REG_EAX; break;
        #if TARGET_IA32E
        case 8:	callback = (AFUNPTR) DATAXFER::sMOV_RM<64>;	regSrc = REG_RAX; break;
        #endif
        }
        
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, regSrc,	// registre source
            IARG_MEMORYWRITE_EA,	// adresse réelle d'ecriture
            IARG_INST_PTR, IARG_END);
    }
} // cSTOS

// pour les instructions CMPS et SCAS, deux préfixes possibles 
// REPE et REPNE, avec (e/r)cx comme compteur
// contrairement à MOVS/LODS/STOS, il est impossible de savoir 
// lors de l'instrumentation si la répétition sera effectuée 
// (hormis le cas ou le compteur est nul) car la répétition dépend 
// du resultat de la comparaison
//
//      L'instrumentation sera donc faite par un PredicatedCall,
//      qui appelera la fonction à chaque itération, sauf si count == 0. 
//      La fonction devra effectuer le marquage pour chaque opération
//		cela va provoquer une série de marquage/demarquage des flags, 
//      avec une déclaration de condition SMTLIB à chaque fois
//		Mais il est impossible de faire autrement
//      Seul avantage : pas d'obligation de passer les flags (DF) en argument

//////////
// SCAS //
//////////
// SCAS fait une comparaison AL/AX/EAX/RAX <-> mem (edi)
//
// pour accélerer le traitement, le marquage du registre va être stocké
// dans une variable globale à la première itération
// Il y aura donc un duo de callback if/then pour stockage du marquage
// et un predicatedcall pour l'instrumentation de l'instruction
// (obligatoirement en dernier callback => IARG_ORDER_CALL = last

// CALLBACKS
void STRINGOP::cSCAS(INS &ins, UINT32 size)
{ 
    void (*callback)() = nullptr;

    REG regSrc = REG_INVALID();	// registre source (AL si 8b, AX si 16b, etc...)
    if (INS_HasRealRep(ins))    // instruction préfixée par REPE ou REPNE
    {	
        void (*firstRepScas)() = nullptr;
        switch (size) 	// taille de l'opérande mémoire de destination
        {
        case 1:	
            callback	= (AFUNPTR) sSCAS<8>;	
            firstRepScas	= (AFUNPTR) sFirstRepScas<8>;
            regSrc = REG_AL;
            break;
        case 2:	
            callback	= (AFUNPTR) sSCAS<16>;	
            firstRepScas	= (AFUNPTR) sFirstRepScas<16>;
            regSrc = REG_AX;
            break;
        case 4:	
            callback	= (AFUNPTR) sSCAS<32>;	
            firstRepScas	= (AFUNPTR) sFirstRepScas<32>;
            regSrc = REG_EAX;
            break;
        #if TARGET_IA32E
        case 8:	
            callback	= (AFUNPTR) sSCAS<64>;	
            firstRepScas	= (AFUNPTR) sFirstRepScas<64>;
            regSrc = REG_RAX;
            break;
        #endif
        }
        // insertion callback IF/THEN pour stockage marquage
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR) returnArg, 
            IARG_FAST_ANALYSIS_CALL,
            IARG_FIRST_REP_ITERATION, 
            IARG_END);
        INS_InsertThenCall(ins, IPOINT_BEFORE, firstRepScas,  
            IARG_THREAD_ID,
            IARG_BOOL, INS_RepPrefix(ins),	// VRAI si REPZ, FAUX si REPNZ
            IARG_REG_VALUE, regSrc,		    // AL/AX/EAX/RAX selon archi
            IARG_INST_PTR,                  // adresse de l'instruction
            IARG_END);

        // insertion callback d'analyse de CHAQUE itération d'instruction
        // SSI le predicat sur ECX/RCX est vrai
        // sinon la fonction n'est pas appelée
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, callback, 
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,		// Adresse de lecture (répétition "n")
            IARG_CALL_ORDER, CALL_ORDER_LAST,   // a appeler apres le IF/THEN
            IARG_END);
    }
    else // pas de préfixe REP : une seule répét = cmp [ESI], AL/AX/EAX/RAX
    {	
        switch (size) 	// taille de l'opérande mémoire source
        {
        case 1:	callback = (AFUNPTR) BINARY::sCMP_RM<8>;  regSrc = REG_AL;  break;
        case 2:	callback = (AFUNPTR) BINARY::sCMP_RM<16>; regSrc = REG_AX;  break;
        case 4:	callback = (AFUNPTR) BINARY::sCMP_RM<32>; regSrc = REG_EAX;	break;
        #if TARGET_IA32E
        case 8:	callback = (AFUNPTR) BINARY::sCMP_RM<64>; regSrc = REG_RAX;	break;
        #endif
        }	
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, regSrc,	// registre source
            IARG_REG_VALUE, regSrc,	// sa valeur 
            IARG_MEMORYREAD_EA,		// adresse réelle de lecture
            IARG_INST_PTR, IARG_END);
    }
} // cSCAS

//////////
// CMPS //
//////////
// CMPS : comparaison mem<->mem (opération [ESI] - [EDI])

// CALLBACKS
void STRINGOP::cCMPS(INS &ins, UINT32 size)
{ 
    void (*callback)() = nullptr;

    switch (size) 
    {	
    case 1:	callback = (AFUNPTR) sCMPS<8>;	break;
    case 2:	callback = (AFUNPTR) sCMPS<16>;	break;
    case 4:	callback = (AFUNPTR) sCMPS<32>;	break;
    #if TARGET_IA32E
    case 8: callback = (AFUNPTR) sCMPS<64>;	break;
    #endif
    }

    // convention pour le type de prefixe associé à CMPS
    // 0 : prefixe REPZ / E   |
    // 1 : prefixe REPNZ / NE | 
    // 2 : aucun préfixe (1 seule répét) => pas de contrainte à déclarer
   
    UINT32 repCode = 2;      // par défaut pas de prefixe
    if (INS_HasRealRep(ins)) // présence d'un prefixe REP
    {
        repCode = INS_RepPrefix(ins) ? 0 : 1; 
    }

    // callback "predicated" (appelée uniquement si ECX/RCX non nul)
    INS_InsertPredicatedCall(ins, IPOINT_BEFORE, callback, 
        IARG_THREAD_ID, 
        IARG_UINT32, repCode,	// code préfixe
        IARG_MEMORYREAD_EA,		// Source 1 (ESI)
        IARG_MEMORYREAD2_EA,	// source 2 (EDI)
        IARG_INST_PTR,
        IARG_END);
} // cCMPS
