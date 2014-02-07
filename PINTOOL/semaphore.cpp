#include "semaphore.h"
#include "TaintManager.h"

void SEMAPHORE::cCMPXCHG(INS &ins)
{
    // CMPXCHG : d'abord une comparaison destination (R ou M) avec AL/AX/EAX/RAX
    // puis 1 MOV selon le resultat de la comparaison
    // Opérande 0 : ModRM:r/m (si reg : regDest)
    // Opérande 1 : reg (dénommé regSrc)
    // Dans les arguments des callbacks, il vaut ajouter la valeur de AL/AX/EAX/RAX
    // Et celle du registre dest (cas RR) pour faire la comparaison.
    void (*callback)() = nullptr;
    REG regSrc = INS_OperandReg(ins, 1);
    REG regRAX = REG_INVALID_; // selon la taille, AL/AX/EAX/RAX

    UINT32 regSrcSize = getRegSize(regSrc);
    if (!regSrcSize) return;	// registre non suivi

    else if (INS_IsMemoryRead(ins)) // CMPXCHG_RM
    {
        switch (regSrcSize) 
        {	
        case 1:	callback = (AFUNPTR) sCMPXCHG_RM<8>;  regRAX = REG_AL; break;
        case 2:	callback = (AFUNPTR) sCMPXCHG_RM<16>; regRAX = REG_AX; break;
        case 4:	callback = (AFUNPTR) sCMPXCHG_RM<32>; regRAX = REG_EAX; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sCMPXCHG_RM<64>; regRAX = REG_RAX; break;
        #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, regSrc, 
            IARG_MEMORYREAD_EA, 
            IARG_REG_VALUE, regRAX,
            CALLBACK_DEBUG IARG_END);      
    }
    else // CMPXCHG_RR
    {
        REG regDest = INS_OperandReg(ins, 0); // registre de destination (comparé à AL/AX/EAX/RAX)
        switch (getRegSize(regDest)) 
        {	
        case 0: return; // non suivi en instrumentation
        case 1:	callback = (AFUNPTR) sCMPXCHG_RR<8>;  regRAX = REG_AL; break;
        case 2:	callback = (AFUNPTR) sCMPXCHG_RR<16>; regRAX = REG_AX; break;
        case 4:	callback = (AFUNPTR) sCMPXCHG_RR<32>; regRAX = REG_EAX; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sCMPXCHG_RR<64>; regRAX = REG_RAX; break;
        #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, regSrc, 
            IARG_UINT32, regDest, 
            IARG_REG_VALUE, regDest,
            IARG_REG_VALUE, regRAX,
            CALLBACK_DEBUG IARG_END);     
    }
} // cCMPXCHG
    
void SEMAPHORE::cCMPXCHG8B(INS &ins)
{
    // CMPXCHG8B (mode x86): d'abord une comparaison EDX:EAX avec m64
    // puis 1 MOV ECX:EBX->m64 ou m64->EDX:EAX selon le resultat de la comparaison 
    // Opérande 0 : Mémoire
    // Dans les arguments des callbacks, il vaut ajouter la valeur de EAX et EDX

    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMPXCHG8B,
        IARG_THREAD_ID,
        IARG_MEMORYREAD_EA, 
        IARG_REG_VALUE, REG_EAX,
        IARG_REG_VALUE, REG_EDX,
        CALLBACK_DEBUG IARG_END); 

} // cCMPXCHG8B

#if TARGET_IA32E

void SEMAPHORE::cCMPXCHG16B(INS &ins)
{
    // CMPXCHG16B (mode x64): d'abord une comparaison RDX:RAX avec m128
    // puis 1 MOV RCX:RBX->m128 ou m128->RDX:RAX selon le resultat de la comparaison 
    // Opérande 0 : Mémoire
    // Dans les arguments des callbacks, il vaut ajouter la valeur de RAX et RDX

    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sCMPXCHG16B,
        IARG_THREAD_ID,
        IARG_MEMORYREAD_EA, 
        IARG_REG_VALUE, REG_RAX,
        IARG_REG_VALUE, REG_RDX,
        CALLBACK_DEBUG IARG_END);  
    
} // cCMPXCHG16B
#endif


void SEMAPHORE::sCMPXCHG8B(THREADID tid, ADDRINT address, ADDRINT regEAXValue, ADDRINT regEDXValue ADDRESS_DEBUG)
{
}


#if TARGET_IA32E
void SEMAPHORE::sCMPXCHG16B(THREADID tid, ADDRINT address, ADDRINT regRAXValue, ADDRINT regRDXValue ADDRESS_DEBUG)
{
}
#endif