#include "PUSH.h"
#include "DATAXFER.h"

//////////
// PUSH //
//////////
// CALLBACKS
void PUSH::cPUSH(INS &ins)
{
    void (*callback)() = nullptr;

    if (INS_OperandIsReg(ins, 0)) // mise d'un registre sur la pile
    {     
        REG reg = INS_OperandReg(ins, 0);
        switch (getRegSize(reg)) 
        {
            
            // case 1:  impossible
            case 2: callback = (AFUNPTR) sPUSH_R<16>;   break;
            case 4: callback = (AFUNPTR) sPUSH_R<32>;   break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sPUSH_R<64>;   break;
            #endif
            default: return; // registre non suivi en marquage
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,  
            IARG_THREAD_ID,
            IARG_UINT32,    reg, // registre source
            IARG_REG_VALUE, REG_STACK_PTR, // valeur d'ESP à ce moment là
            CALLBACK_DEBUG IARG_END);
    }
    else if (INS_OperandIsImmediate(ins, 0)) // mise sur la pile d'une valeur immédiate
    {  
        switch (INS_MemoryWriteSize(ins)) 
        {
            // case 1:  impossible
            case 2: callback = (AFUNPTR) sPUSH_I<16>;   break;
            case 4: callback = (AFUNPTR) sPUSH_I<32>;   break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sPUSH_I<64>;   break;
            #endif
            default: return;    
        }
        
        INS_InsertCall (ins, IPOINT_BEFORE, callback, 
            IARG_THREAD_ID,
            IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'ESP à ce moment là   
            CALLBACK_DEBUG IARG_END);
    }
    else // mise d'une valeur en mémoire sur la pile
    {      
        switch (INS_MemoryWriteSize(ins)) 
        {
            // case 1:  impossible
            case 2: callback = (AFUNPTR) sPUSH_M<16>;   break;
            case 4: callback = (AFUNPTR) sPUSH_M<32>;   break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sPUSH_M<64>;   break;
            #endif
            default: return;
        }
        
        INS_InsertCall (ins, IPOINT_BEFORE, callback,  
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,             // adresse réelle de lecture
            IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'ESP à ce moment là 
            CALLBACK_DEBUG IARG_END);
    }
} // cPUSH

#if TARGET_IA32 // PUSHA et PUSHAD valables uniquement en 32bits
void PUSH::cPUSHA(INS &ins)
{  
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sPUSHA,  
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'ESP à ce moment là
        CALLBACK_DEBUG IARG_END);
} // cPUSHA

void PUSH::cPUSHAD(INS &ins)
{ 
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sPUSHAD,  
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'ESP à ce moment là
        CALLBACK_DEBUG IARG_END);
} // cPUSHAD

void PUSH::sPUSHA(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{ 
    // mise sur la pile des registres dans l'ordre AX, CX, DX, BX, SP (original), BP, SI, et DI
    // du point de vue marquage, equivalent à un MOVRM [SP-2], reg 

    REG regsToPush[8] = {REG_AX, REG_CX, REG_DX, REG_BX, REG_SP, REG_BP, REG_SI, REG_DI};
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));    
    
    // sauvegarde du marquage de SP. Sauvegarde par octet pour éviter de devoir récupérer la valeur numérique de SP
    std::vector<TaintBytePtr> savedSP;  
    savedSP.push_back(pTmgrTls->getRegisterPartTaint(rESP, 0)); // objet marqué ou nullptr;
    savedSP.push_back(pTmgrTls->getRegisterPartTaint(rESP, 1)); // objet marqué ou nullptr;
  
    ADDRINT spAddress = stackAddressBeforePush - 2; // adresse de départ : SP-2 pour le 1er registre
    
    for (UINT32 tabIndex = 0 ; tabIndex < 8 ; ++tabIndex, spAddress -= 2)
    {
        REG reg = regsToPush[tabIndex];
        
        // cas particulier du SP : traitement direct
        if (reg == REG_SP)
        {
            ADDRINT addressForPushingSP = spAddress; // sauvegarde de l'adresse de départ pour SP
            
            auto itEnd = savedSP.end();
            for (auto it = savedSP.begin() ; it != itEnd ; ++it, ++addressForPushingSP)
            {
                if ((bool) *it) pTmgrGlobal->updateMemoryTaint<8>(addressForPushingSP, *it);
                else pTmgrGlobal->unTaintMemory<8>(addressForPushingSP);
            } 
        }
        // Sinon, simulation du PUSH du registre
        else DATAXFER::sMOV_RM<16>(tid, reg, spAddress INSADDRESS); 
    } 

    // mise à jour du marquage du REGISTRE SP, dans le cas où il est marqué avant le PUSHA
    if (pTmgrTls->isRegisterTainted<16>(REG_SP))
    {
        // nouvel objet = SP - (longueur pushée), soit 8*2 octets pour PUSHA
        pTmgrTls->updateTaintRegister<16>(REG_SP, std::make_shared<TaintWord>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<16>(REG_SP, stackAddressBeforePush)),
            ObjectSource(16, 8*2)));
    }
} // sPUSHA

void PUSH::sPUSHAD(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{ 
    // mise sur la pile des registres dans l'ordre EAX, ECX, EDX, EBX, ESP (orig.), EBP, ESI, EDI
    // du point de vue marquage, equivalent à un MOVRM [ESP-4], reg si reg marqué, sinon démarquage

    REG regsToPush[8] = {REG_EAX, REG_ECX, REG_EDX, REG_EBX, REG_ESP, REG_EBP, REG_ESI, REG_EDI};
    
    // sauvegarde du marquage de ESP
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));    
    
    // sauvegarde du marquage de SP. Sauvegarde par octet pour éviter de devoir récupérer la valeur numérique de SP
    std::vector<TaintBytePtr> savedESP;  
    for (UINT32 regPart = 0 ; regPart < 4; ++regPart)  
    {
        savedESP.push_back(pTmgrTls->getRegisterPartTaint(rESP, regPart)); // objet marqué ou nullptr;
    }

    ADDRINT espAddress = stackAddressBeforePush - 4; // adresse de départ : ESP-4 pour le 1er registre
    
    for (UINT32 tabIndex = 0 ; tabIndex < 8 ; ++tabIndex, espAddress -= 4)
    {
        REG reg = regsToPush[tabIndex];
        
        // cas particulier d'ESP : traitement direct
        if (reg == REG_ESP)
        {
            ADDRINT addressForPushingESP = espAddress; // sauvegarde de l'adresse de départ pour SP
            
            auto itEnd = savedESP.end();
            for (auto it = savedESP.begin() ; it != itEnd ; ++it, ++addressForPushingESP)
            {
                if ((bool) *it) pTmgrGlobal->updateMemoryTaint<8>(addressForPushingESP, *it);
                else pTmgrGlobal->unTaintMemory<8>(addressForPushingESP);
            }
        }
        // Sinon, simulation du PUSH du registre
        else DATAXFER::sMOV_RM<32>(tid, reg, espAddress INSADDRESS); 
    } 
    
    // mise à jour du marquage du REGISTRE ESP, dans le cas où il est marqué avant le PUSHA
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP - (longueur pushée), soit 8*4 octets pour PUSHAD
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(32, 8*4)));
    }
} // sPUSHAD
#endif

void PUSH::cPUSHF(INS &ins)
{  
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sPUSHF,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_STACK_PTR,          // valeur d'ESP à ce moment là
        CALLBACK_DEBUG IARG_END);
} // cPUSHF

void PUSH::sPUSHF(THREADID tid, ADDRINT espAddress ADDRESS_DEBUG) 
{  
    // Eflags mis sur la pile (on ne s'intéresse qu'aux bits 0 à 15)

}
