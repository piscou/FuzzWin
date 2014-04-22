#include "misc.h"
#include <TaintUtilities\utils.h>

/////////
// LEA //
/////////
// CALLBACKS
void MISC::cLEA(INS &ins) 
{
    REG regDest        = INS_RegW(ins, 0);               // registre de destination 
    UINT32 regDestSize = getRegSize(regDest);            // taille du registre dest ("Operand Size") 
    UINT32 addrSize    = INS_EffectiveAddressWidth(ins); // taille de l'adresse ("Address Size")
    void (*callback)() = nullptr;                        // pointeur sur la fonction a appeler
    
    // 1ER TEMPS : calcul de l'objet représentant l'adresse effective utilisée.
    // cela va insérer une fonction d'instrumentation qui va stocker l'objet dans TaintManager
    UTILS::cGetKindOfEA(ins);

    // seconde fonction d'analyse selon le couple OpSize/AddrSize
    
#if TARGET_IA32
    /** CAS 32BITS : 16/16, 16/32, 32/16 et 32/32 **/
    // cas 16/??
    if      (regDestSize == 2) callback = (AFUNPTR) ((16 == addrSize) ? sLEA<16,16> : sLEA<16,32>);
    // cas 32/??
    else if (regDestSize == 4) callback = (AFUNPTR) ((16 == addrSize) ? sLEA<32,16> : sLEA<32,32>);
    // si le registre destination n'est pas géré, ne pas instrumenter
    else return; 
#else
    /** CAS 64BITS : 16/32, 16/64, 32/32, 32/64, 64/32, 64/64 **/
    // cas 16/??
    if      (regDestSize == 2) callback = (AFUNPTR) ((32 == addrSize) ? sLEA<16,32> : sLEA<16,64>);
    // cas 32/??
    else if (regDestSize == 4) callback = (AFUNPTR) ((32 == addrSize) ? sLEA<32,32> : sLEA<16,64>);
    // cas 64/??
    else if (regDestSize == 8) callback = (AFUNPTR) ((32 == addrSize) ? sLEA<32,32> : sLEA<32,64>);
    // si le registre destination n'est pas géré, ne pas instrumenter
    else return; 
#endif

    INS_InsertCall(ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regDest, // registre de destination 
                IARG_INST_PTR, IARG_END);
}   // sLEA

///////////
// LEAVE //
///////////

#if TARGET_IA32
void MISC::cLEAVE(INS &ins) 
{
    // LEAVE (32bits) <=> MOV (E)SP, (E)BP + POP (E)BP (POP simulé en MOVMR)
    // par défaut sur 32 bits
    void (*cMOV)() = (AFUNPTR) DATAXFER::sMOV_RR<32>;
    void (*cPOP)() = (AFUNPTR) DATAXFER::sMOV_MR<32>;
    REG regEbp = REG_EBP;
    REG regEsp = REG_ESP;
 
    if (INS_MemoryReadSize(ins) == 2) // sur 16bit : changement en BP et SP
    {
        cMOV = (AFUNPTR) DATAXFER::sMOV_RR<16>;
        cPOP = (AFUNPTR) DATAXFER::sMOV_MR<16>;
        regEbp = REG_BP;
        regEsp = REG_SP;
    }

    INS_InsertCall(ins, IPOINT_BEFORE, cMOV,
        IARG_CALL_ORDER, CALL_ORDER_FIRST,
        IARG_THREAD_ID,
        IARG_UINT32, regEbp,   // registre source = (E)BP
        IARG_UINT32, regEsp,   // registre de destination = (E)SP 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall(ins, IPOINT_BEFORE, cPOP,
        IARG_CALL_ORDER, CALL_ORDER_LAST,
        IARG_THREAD_ID,
        IARG_REG_VALUE, regEbp, // ATTENTION : valeur d'ESP à ce moment là  = EBP (suite au MOV plus haut) 
        IARG_UINT32,    regEbp, // registre de destination
        IARG_INST_PTR, IARG_END);
}
#else
void MISC::cLEAVE(INS &ins) 
{
    // LEAVE (64bits) <=> MOV RSP, RBP + POP RBP (POP simulé en MOVMR)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) DATAXFER::sMOV_RR<64>,
        IARG_CALL_ORDER, CALL_ORDER_FIRST,
        IARG_THREAD_ID,
        IARG_UINT32, REG_RBP,   // registre source = RBP
        IARG_UINT32, REG_RSP,   // registre de destination = RSP 
        IARG_INST_PTR, IARG_END);

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) DATAXFER::sMOV_MR<64>,
        IARG_CALL_ORDER, CALL_ORDER_LAST,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_RBP, // ATTENTION : valeur d'ESP à ce moment là  = EBP (suite au MOV plus haut)
        IARG_UINT32,    REG_RBP, // registre de destination
        IARG_INST_PTR, IARG_END);
}
#endif

//////////
// XLAT //
//////////

void MISC::cXLAT(INS &ins) 
{
    // XLAT est un MOV Memoire -> registre (8BITS), ou l'emplacement
    // mémoire est défini par DS:(E/R)BX + ZeroExtend(AL)

    // TODO : traiter le cas où (E/R)BX ou AL est marqué
    // (adressage indirect)

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) DATAXFER::sMOV_MR<8>,
        IARG_THREAD_ID,
        IARG_MEMORYREAD_EA,  // emplacement mémoire de lecture
        IARG_UINT32, REG_AL, // registre destination = AL
        IARG_INST_PTR, IARG_END);
}

///////////
// CPUID //
///////////

// CALLBACK
void MISC::cCPUID(INS &ins)
{
    // démarquage E/RAX, E/RBX, E/RCX et E/RDX
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sCPUID,
        IARG_FAST_ANALYSIS_CALL,
        IARG_THREAD_ID,
        IARG_INST_PTR, IARG_END);
}

// SIMULATE

void PIN_FAST_ANALYSIS_CALL MISC::sCPUID(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

#if TARGET_IA32
    // 32bits : démarquage EAX, EBX, ECX et EDX
    pTmgrTls->unTaintRegister<32>(REG_EAX);
    pTmgrTls->unTaintRegister<32>(REG_EBX);
    pTmgrTls->unTaintRegister<32>(REG_ECX);
    pTmgrTls->unTaintRegister<32>(REG_EDX);
#else
    // 32bits : démarquage RAX, RBX, RCX et RDX
    pTmgrTls->unTaintRegister<64>(REG_RAX);
    pTmgrTls->unTaintRegister<64>(REG_RBX);
    pTmgrTls->unTaintRegister<64>(REG_RCX);
    pTmgrTls->unTaintRegister<64>(REG_RDX);
#endif
}
