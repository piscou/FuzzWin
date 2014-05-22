#include "instrumentation.h"
#include <Translate\translate.h>
#include <Syscalls\syscalls.h>
#include <TaintUtilities\utils.h>

#include <Binary\binary.h>
#include <Bitbyte\bitbyte.h>
#include <Cmov\cmov.h>
#include <Call\call.h>
#include <ConditionalBranch\conditional_branch.h>
#include <Convert\convert.h>
#include <Decimal\decimal.h>
#include <UnconditionalBranch\unconditional_branch.h>
#include <Dataxfer\dataxfer.h>
#include <Flagop\flagop.h>
#include <Logical\logical.h>
#include <Misc\misc.h>
#include <Pop\pop.h>
#include <Push\push.h>
#include <Shift\shift.h>
#include <Ret\ret.h>
#include <Rotate\rotate.h>
#include <StringOp\stringop.h>
#include <Semaphore\semaphore.h>

/*********************/
/*** PINTOOL TAINT ***/
/*********************/

// Fonction d'instrumentation des instructions
// premier tri en fonction du nom de l'instruction, qui orientera vers les
// procédures spécifiques à chaque instruction
// les instructions sont regroupées en CATEGORIES (fichiers .cpp, .hpp et .h)
// ces catégories sont celles définies par PIN
void INSTRUMENTATION::Instruction(INS ins, void* )
{
    if (!g_beginInstrumentationOfInstructions) return;

    // mode VERBOSE : désassemblage 
    _LOGINS(ins); 

    switch (INS_Opcode(ins)) // BIG BIG SWITCH :)
    {
    
    // BINARY: ADD, SUB, INC, DEC, NEG, CMP
    case XED_ICLASS_SUB:  BINARY::cSUB(ins);  break;
    case XED_ICLASS_ADC:  BINARY::cADC(ins);  break;
    case XED_ICLASS_SBB:  BINARY::cSBB(ins);  break;
    case XED_ICLASS_ADD:  BINARY::cADD(ins);  break;
    case XED_ICLASS_INC:  BINARY::cINC(ins);  break;
    case XED_ICLASS_DEC:  BINARY::cDEC(ins);  break;
    case XED_ICLASS_CMP:  BINARY::cCMP(ins);  break;
    case XED_ICLASS_NEG:  BINARY::cNEG(ins);  break;
    case XED_ICLASS_MUL:  BINARY::cMUL(ins); break;
    case XED_ICLASS_IMUL: BINARY::cIMUL(ins); break;
    case XED_ICLASS_IDIV: BINARY::cDIVISION(ins, true); break;  // true = signed
    case XED_ICLASS_DIV:  BINARY::cDIVISION(ins, false); break; // false = unsigned

    // BIBYTE (SETcc)
    case XED_ICLASS_SETB:   BITBYTE::cSETB(ins);    break;
    case XED_ICLASS_SETNB:  BITBYTE::cSETNB(ins);   break;
    case XED_ICLASS_SETO:   BITBYTE::cSETO(ins);    break;
    case XED_ICLASS_SETNO:  BITBYTE::cSETNO(ins);   break;
    case XED_ICLASS_SETP:   BITBYTE::cSETP(ins);    break;
    case XED_ICLASS_SETNP:  BITBYTE::cSETNP(ins);   break;
    case XED_ICLASS_SETS:   BITBYTE::cSETS(ins);    break;
    case XED_ICLASS_SETNS:  BITBYTE::cSETNS(ins);   break;
    case XED_ICLASS_SETZ:   BITBYTE::cSETZ(ins);    break;
    case XED_ICLASS_SETNZ:  BITBYTE::cSETNZ(ins);   break;
    case XED_ICLASS_SETBE:  BITBYTE::cSETBE(ins);   break;
    case XED_ICLASS_SETNBE: BITBYTE::cSETNBE(ins);  break;
    case XED_ICLASS_SETL:   BITBYTE::cSETL(ins);    break;
    case XED_ICLASS_SETNL:  BITBYTE::cSETNL(ins);   break;
    case XED_ICLASS_SETLE:  BITBYTE::cSETLE(ins);   break;
    case XED_ICLASS_SETNLE: BITBYTE::cSETNLE(ins);  break;    
    // BITBYTE (BTxx, BSR, BSF)
    case XED_ICLASS_BT:  BITBYTE::cBT(ins);  break;
    case XED_ICLASS_BTC: BITBYTE::cBTC(ins); break;
    case XED_ICLASS_BTR: BITBYTE::cBTR(ins); break;
    case XED_ICLASS_BTS: BITBYTE::cBTS(ins); break;
    case XED_ICLASS_BSR: BITBYTE::cBSR(ins); break;
    case XED_ICLASS_BSF: BITBYTE::cBSF(ins); break;

    // CMOV
    case XED_ICLASS_CMOVB:   CMOV::cCMOVB(ins);    break;
    case XED_ICLASS_CMOVNB:  CMOV::cCMOVNB(ins);   break;
    case XED_ICLASS_CMOVO:   CMOV::cCMOVO(ins);    break;
    case XED_ICLASS_CMOVNO:  CMOV::cCMOVNO(ins);   break;
    case XED_ICLASS_CMOVP:   CMOV::cCMOVP(ins);    break;
    case XED_ICLASS_CMOVNP:  CMOV::cCMOVNP(ins);   break;
    case XED_ICLASS_CMOVS:   CMOV::cCMOVS(ins);    break;
    case XED_ICLASS_CMOVNS:  CMOV::cCMOVNS(ins);   break;
    case XED_ICLASS_CMOVZ:   CMOV::cCMOVZ(ins);    break;
    case XED_ICLASS_CMOVNZ:  CMOV::cCMOVNZ(ins);   break;
    case XED_ICLASS_CMOVBE:  CMOV::cCMOVBE(ins);   break;
    case XED_ICLASS_CMOVNBE: CMOV::cCMOVNBE(ins);  break;
    case XED_ICLASS_CMOVL:   CMOV::cCMOVL(ins);    break;
    case XED_ICLASS_CMOVNL:  CMOV::cCMOVNL(ins);   break;
    case XED_ICLASS_CMOVLE:  CMOV::cCMOVLE(ins);   break;
    case XED_ICLASS_CMOVNLE: CMOV::cCMOVNLE(ins);  break;

    // CONDITIONAL_BRANCH   
    case XED_ICLASS_JB:     CONDITIONAL_BR::cJB(ins);   break;
    case XED_ICLASS_JNB:    CONDITIONAL_BR::cJNB(ins);  break;
    case XED_ICLASS_JO:     CONDITIONAL_BR::cJO(ins);   break;
    case XED_ICLASS_JNO:    CONDITIONAL_BR::cJNO(ins);  break;
    case XED_ICLASS_JP:     CONDITIONAL_BR::cJP(ins);   break;
    case XED_ICLASS_JNP:    CONDITIONAL_BR::cJNP(ins);  break;
    case XED_ICLASS_JS:     CONDITIONAL_BR::cJS(ins);   break;
    case XED_ICLASS_JNS:    CONDITIONAL_BR::cJNS(ins);  break;
    case XED_ICLASS_JZ:     CONDITIONAL_BR::cJZ(ins);   break;
    case XED_ICLASS_JNZ:    CONDITIONAL_BR::cJNZ(ins);  break;
    case XED_ICLASS_JBE:    CONDITIONAL_BR::cJBE(ins);  break;
    case XED_ICLASS_JNBE:   CONDITIONAL_BR::cJNBE(ins); break;
    case XED_ICLASS_JL:     CONDITIONAL_BR::cJL(ins);   break;
    case XED_ICLASS_JNL:    CONDITIONAL_BR::cJNL(ins);  break;
    case XED_ICLASS_JLE:    CONDITIONAL_BR::cJLE(ins);  break;
    case XED_ICLASS_JNLE:   CONDITIONAL_BR::cJNLE(ins); break;
    case XED_ICLASS_JRCXZ:  CONDITIONAL_BR::cJRCXZ(ins); break;
    case XED_ICLASS_LOOP:   CONDITIONAL_BR::cLOOP(ins);  break;
    case XED_ICLASS_LOOPE:  CONDITIONAL_BR::cLOOPE(ins); break;
    case XED_ICLASS_LOOPNE: CONDITIONAL_BR::cLOOPNE(ins);break;
   
    // CONVERT
    case XED_ICLASS_CBW:  CONVERT::cCBW(ins);  break;
    case XED_ICLASS_CWDE: CONVERT::cCWDE(ins); break;
    case XED_ICLASS_CWD:  CONVERT::cCWD(ins);  break;
    case XED_ICLASS_CDQ:  CONVERT::cCDQ(ins);  break;
#if TARGET_IA32E
    case XED_ICLASS_CDQE: CONVERT::cCDQE(ins); break;
    case XED_ICLASS_CQO:  CONVERT::cCQO(ins);  break;
#endif

    // DATAXFER: MOV, MOVSX, MOVZX, XCHG, BSWAP
    case XED_ICLASS_MOV:   DATAXFER::cMOV(ins);   break;
    case XED_ICLASS_MOVSX: DATAXFER::cMOVSX(ins); break;
    case XED_ICLASS_MOVZX: DATAXFER::cMOVZX(ins); break;
    case XED_ICLASS_XCHG:  DATAXFER::cXCHG(ins);  break;
    case XED_ICLASS_BSWAP: DATAXFER::cBSWAP(ins); break;
    #if TARGET_IA32E
    case XED_ICLASS_MOVSXD: DATAXFER::cMOVSXD(ins);  break;
    #endif 

    // DECIMAL (uniquement en x86)
#if TARGET_IA32
    case XED_ICLASS_AAA:  DECIMAL::cAAA(ins); break;
    case XED_ICLASS_AAD:  DECIMAL::cAAD(ins); break;
    case XED_ICLASS_AAM:  DECIMAL::cAAM(ins); break;
    case XED_ICLASS_AAS:  DECIMAL::cAAS(ins); break;
    case XED_ICLASS_DAA:  DECIMAL::cDAA(ins); break;
    case XED_ICLASS_DAS:  DECIMAL::cDAS(ins); break;
#endif

    // FLAGOP
    case XED_ICLASS_CLC: // CLC et STC ont le même effet : démarquage CF uniquement
    case XED_ICLASS_STC:    FLAGOP::cCLC_STC(ins); break;

    case XED_ICLASS_CMC:    FLAGOP::cCMC(ins);  break;
    case XED_ICLASS_LAHF:   FLAGOP::cLAHF(ins); break;
    case XED_ICLASS_SAHF:   FLAGOP::cSAHF(ins); break;
    case XED_ICLASS_SALC:   FLAGOP::cSALC(ins); break;
    case XED_ICLASS_CLD:    break;  // Direction Flag mis à 0, sans objet pour le marquage
    case XED_ICLASS_CLI:    break;  // Interrupt Flag mis à 0, sans objet pour le marquage
    case XED_ICLASS_STD:    break;  // Direction Flag mis à 1, sans objet pour le marquage
    case XED_ICLASS_STI:    break;  // Interrupt Flag mis à 1, sans objet pour le marquage

    // SHIFT: SHL, SHR, SAR, SHRD, SHLD
    case XED_ICLASS_SHL:  SHIFT::cSHL(ins);  break;
    case XED_ICLASS_SHR:  SHIFT::cSHR(ins);  break;
    case XED_ICLASS_SAR:  SHIFT::cSAR(ins);  break;
    case XED_ICLASS_SHRD: SHIFT::cSHRD(ins); break;
    case XED_ICLASS_SHLD: SHIFT::cSHLD(ins); break;

    // LOGICAL: AND, NOT, OR, TEST, XOR
    case XED_ICLASS_NOT:  LOGICAL::cNOT(ins);  break;
    case XED_ICLASS_AND:  LOGICAL::cAND(ins);  break;
    case XED_ICLASS_OR:   LOGICAL::cOR(ins);   break;
    case XED_ICLASS_XOR:  LOGICAL::cXOR(ins);  break;
    case XED_ICLASS_TEST: LOGICAL::cTEST(ins); break;

    // PUSH:
    case XED_ICLASS_PUSH:   PUSH::cPUSH(ins);     break;
    case XED_ICLASS_PUSHF:  PUSH::cPUSHF(ins, 2); break;
    case XED_ICLASS_PUSHFD: PUSH::cPUSHF(ins, 4); break;
#if TARGET_IA32
    case XED_ICLASS_PUSHA:  PUSH::cPUSHA(ins);    break;
    case XED_ICLASS_PUSHAD: PUSH::cPUSHAD(ins);   break;
#endif
#if TARGET_IA32E
    case XED_ICLASS_PUSHFQ: PUSH::cPUSHF(ins, 8); break;
#endif
     
    // POP:  
    case XED_ICLASS_POP:   POP::cPOP(ins);     break;
    case XED_ICLASS_POPF:  POP::cPOPF(ins, 2); break;
    case XED_ICLASS_POPFD: POP::cPOPF(ins, 4); break;
#if TARGET_IA32
    case XED_ICLASS_POPA:  POP::cPOPA(ins);    break;
    case XED_ICLASS_POPAD: POP::cPOPAD(ins);   break;
#endif
#if TARGET_IA32E
    case XED_ICLASS_POPFQ: POP::cPOPF(ins, 8); break;
#endif

    // MISC
    case XED_ICLASS_LEA:    MISC::cLEA(ins);    break;
    case XED_ICLASS_LEAVE:  MISC::cLEAVE(ins);  break;
    case XED_ICLASS_XLAT:   MISC::cXLAT(ins);   break;
    case XED_ICLASS_PAUSE:  break;      // identique à NOP
    case XED_ICLASS_CPUID:  MISC::cCPUID(ins);  break;
    
    // RET
    case XED_ICLASS_RET_FAR:    RET::cRET(ins, true); break;  // true  <=> FAR RET
    case XED_ICLASS_RET_NEAR:   RET::cRET(ins, false); break;  // false  <=> NEAR RET

    // STRINGOP: le second argument est la taille des opérandes, en octets
    //case XED_ICLASS_CMPSB:  STRINGOP::cCMPS(ins, 1);  break;
    case XED_ICLASS_CMPSW:  STRINGOP::cCMPS(ins, 2);  break;
    case XED_ICLASS_CMPSD:  STRINGOP::cCMPS(ins, 4);  break;
        
    case XED_ICLASS_LODSB:  STRINGOP::cLODS(ins, 1);  break;
    case XED_ICLASS_LODSW:  STRINGOP::cLODS(ins, 2);  break;
    case XED_ICLASS_LODSD:  STRINGOP::cLODS(ins, 4);  break;

    case XED_ICLASS_MOVSB:  STRINGOP::cMOVS(ins, 1);  break;
    case XED_ICLASS_MOVSW:  STRINGOP::cMOVS(ins, 2);  break;
    case XED_ICLASS_MOVSD:  STRINGOP::cMOVS(ins, 4);  break;

    case XED_ICLASS_SCASB:  STRINGOP::cSCAS(ins, 1);  break;
    case XED_ICLASS_SCASW:  STRINGOP::cSCAS(ins, 2);  break;
    case XED_ICLASS_SCASD:  STRINGOP::cSCAS(ins, 4);  break;

    case XED_ICLASS_STOSB:  STRINGOP::cSTOS(ins, 1);  break;
    case XED_ICLASS_STOSW:  STRINGOP::cSTOS(ins, 2);  break;
    case XED_ICLASS_STOSD:  STRINGOP::cSTOS(ins, 4);  break;

    #if TARGET_IA32E
    case XED_ICLASS_CMPSQ:  STRINGOP::cCMPS(ins, 8);  break;
    case XED_ICLASS_LODSQ:  STRINGOP::cLODS(ins, 8);  break;
    case XED_ICLASS_MOVSQ:  STRINGOP::cMOVS(ins, 8);  break;
    case XED_ICLASS_SCASQ:  STRINGOP::cSCAS(ins, 8);  break;
    case XED_ICLASS_STOSQ:  STRINGOP::cSTOS(ins, 8);  break;
    #endif

    // CALL 
    case XED_ICLASS_CALL_FAR:  CALL::cCALL(ins, true); break;  // true  <=> FAR CALL
    case XED_ICLASS_CALL_NEAR: CALL::cCALL(ins, false); break; // false <=> NEAR CALL

    // UNCONDITIONAL_BR
    case XED_ICLASS_JMP: UNCONDITIONAL_BR::cJMP(ins); break;
    // les JMP_FAR ne sont pas traités pour l'instant
    case XED_ICLASS_JMP_FAR: _LOGDEBUG(" *** JMP_FAR ***"); break;

    
    // SEMAPHORE
    case XED_ICLASS_CMPXCHG:    SEMAPHORE::cCMPXCHG(ins); break;
    case XED_ICLASS_CMPXCHG8B:  SEMAPHORE::cCMPXCHG8B(ins); break;
#if TARGET_IA32E
    case XED_ICLASS_CMPXCHG16B: SEMAPHORE::cCMPXCHG16B(ins); break;
#endif
    case XED_ICLASS_XADD:       SEMAPHORE::cXADD(ins);  break;  

    // ROTATE
    case XED_ICLASS_ROL: ROTATE::cROL(ins); break;
    case XED_ICLASS_ROR: ROTATE::cROR(ins); break;
    case XED_ICLASS_RCL: ROTATE::cRCL(ins); break;
    case XED_ICLASS_RCR: ROTATE::cRCR(ins); break;
    
    /*** AUCUNE ACTION SUR MEMOIRE OU REGISTRE MARQUE : NE RIEN FAIRE ***/
    case XED_ICLASS_NOP:    break;    // la plus facile :p

    /*** AUTRES INSTRUCTIONS : DEMARQUAGE DES DESTINATIONS SUIVIES ***/
    default: 
        UTILS::cUNHANDLED(ins);     
        if (g_verbose)
        {
            PIN_GetLock(&g_lock, PIN_ThreadId()); 
            g_debug << " *** non instrumenté ***"; 
            PIN_ReleaseLock(&g_lock); 
        }
        break;
    }
    _LOGDEBUG(""); // juste un retour chariot
}

// Fonction de notification lors de la fin de l'exécution
void INSTRUMENTATION::FiniTaint(INT32 code, void* ) 
{
    PIN_GetLock(&g_lock, 0);
    
    // envoi des dernieres données récoltées
    g_pFormula->final();

    // fermeture fichier de logs 
    if (g_verbose)
    {
        clock_t totalTime = clock() - g_timeBegin;

        g_debug << "Temps ecoule (ticks) : " << decstr(totalTime);
        g_debug << " soit " << ((float) totalTime)/CLOCKS_PER_SEC << " secondes" << std::endl;
        g_debug << "CODE DE FIN : " << code << std::endl;
        g_debug << "#eof\n";    
        g_debug.close(); 
        
        g_taint << "#eof\n";    
        g_taint.close();
    }


    // flush puis déconnexion du pipe, si pipe présent
    if (!g_nopipe)
    {
        WINDOWS::FlushFileBuffers(g_hPipe);
        WINDOWS::CloseHandle(g_hPipe);     
    } 

    // libération des classes globales
    delete (pTmgrGlobal);
    delete (g_pFormula);

    // libération des slots de la TLS
    PIN_DeleteThreadDataKey(g_tlsKeyTaint);
    PIN_DeleteThreadDataKey(g_tlsKeySyscallData);

    // Libération du verrou
    PIN_ReleaseLock(&g_lock);

    // fin forcée (sans attendre le thread "maxtime" s'il s'exécute encore)
    PIN_ExitProcess(code);
}

// Fonction de notification lors du lancement d'un thread
void INSTRUMENTATION::threadStart(THREADID tid, CONTEXT *, INT32 , VOID *)
{
    _LOGDEBUG("Création du thread n° " + decstr(tid) + " et TLS associée");

    TaintManager_Thread *pTmgrTls = new TaintManager_Thread;
    Syscall_Data *pSyscallData    = new Syscall_Data;
    StringOpInfo *pStringOpInfo   = new StringOpInfo;

    PIN_SetThreadData(g_tlsKeyTaint, pTmgrTls, tid);
    PIN_SetThreadData(g_tlsKeySyscallData, pSyscallData, tid);
    PIN_SetThreadData(g_tlsStringOpInfo, pStringOpInfo, tid);
}

// Fonction de notification lors de la fin d'un thread
void INSTRUMENTATION::threadFini(THREADID tid, const CONTEXT *, INT32 , VOID *)
{
    _LOGDEBUG("destruction du thread n° " + decstr(tid) + " et TLS associée");

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    delete (pTmgrTls);

    Syscall_Data *pSysData = 
        static_cast<Syscall_Data*>(PIN_GetThreadData(g_tlsKeySyscallData, tid));
    delete (pSysData);

    StringOpInfo *pStringOpInfo =  
        static_cast<StringOpInfo*>(PIN_GetThreadData(g_tlsStringOpInfo, tid));
    delete (pStringOpInfo);
}

/*** INSTRUMENTATION DES IMAGES ***/

void INSTRUMENTATION::Image(IMG img, void *)
{
    // recherche de NtQueryObject uniquement dans NtDll.dll
    if (std::string::npos == IMG_Name(img).find("ntdll.dll")) return;

    RTN NtQueryObjectRtn = RTN_FindByName(img, "NtQueryObject");

    g_AddressOfNtQueryObject = reinterpret_cast<t_NtQueryObject>(RTN_Funptr(NtQueryObjectRtn));
    if (g_AddressOfNtQueryObject) _LOGDEBUG("Adresse de NtQueryObject = " + hexstr(*(ADDRINT*) g_AddressOfNtQueryObject));
}


/**************************/
/*** PINTOOL CHECKSCORE ***/
/**************************/

// Fonction de notification lors du changement de contexte
void INSTRUMENTATION::changeCtx
    (THREADID, CONTEXT_CHANGE_REASON reason, const CONTEXT* , CONTEXT* , INT32 sig, VOID*) 
{
    if (reason == CONTEXT_CHANGE_REASON_EXCEPTION) 
    {
        // => erreur
        PIN_GetLock(&g_lock, PIN_GetTid());
        g_faultFound = true;
        PIN_ReleaseLock(&g_lock);

        // appel de la fonction "FiniCheckscore" avant de quitter le programme
        PIN_ExitApplication(EXIT_EXCEPTION); 
    }
}

// Fonction de notification lors de la fin de l'exécution
void INSTRUMENTATION::FiniCheckScore(INT32 code, void* ) 
{
    WINDOWS::DWORD cbWritten;
    std::string message; // par défaut, aucun score (= faute trouvée)

    // si exception, le message sera '0'
    // sinon ce sera le nombre d'instructions exécutées
    if (g_faultFound) message = "0";
    else
    {
        UINT64 totalIns = 0;
        
        // somme des instructions de tous les threads
        for (UINT32 t = 0; t < g_numThreads; ++t) totalIns += g_icount[t]._count;
        
        message = decstr(totalIns);
    }

    // envoi du resultat en entier dans le pipe  (= stdout en mode nopipe)
    WINDOWS::WriteFile(g_hPipe, 
        message.c_str(), 
        static_cast<WINDOWS::DWORD>(message.size()), // cast pour eviter C4267 en x64 
        &cbWritten, 
        NULL);
    WINDOWS::FlushFileBuffers(g_hPipe);

    // fin forcée (sans attendre le thread "maxtime" s'il s'exécute encore)
    PIN_ExitProcess(code);
}

// fonction d'analyse qui compte le nombre d'instruction de chaque BBL
VOID PIN_FAST_ANALYSIS_CALL INSTRUMENTATION::docount(THREADID tid, ADDRINT bblCount)
{ 
    g_icount[tid]._count += bblCount; 
}

// Fonction d'instrumentation des traces
// ajout du nombre d'instructions de la trace au total
void INSTRUMENTATION::traceCheckScore(TRACE trace, VOID *)
{
    for (BBL bbl = TRACE_BblHead(trace) ; BBL_Valid(bbl) ; bbl = BBL_Next(bbl))
    {
        BBL_InsertCall(bbl, IPOINT_ANYWHERE, (AFUNPTR) docount, 
            IARG_FAST_ANALYSIS_CALL,
            IARG_THREAD_ID,
            IARG_UINT32, BBL_NumIns(bbl),  
            IARG_END); 
    }   
}

// Fonction de notification lors du lancement d'un nouveau thread
void INSTRUMENTATION::ThreadStartCheckScore(THREADID tid, CONTEXT *, INT32 , VOID *)
{
    ++g_numThreads;
}