#include "pop.h"
#include <Dataxfer\dataxfer.h> // POP_R

/////////
// POP //
/////////

// CALLBACKS
void POP::cPOP(INS &ins) 
{
    void (*callback)() = nullptr;
    if (INS_OperandIsReg(ins, 0)) 
    {     
        // désempilement vers registre, équivalengthInBitst à MOVMR
        REG reg = INS_OperandReg(ins, 0);
        switch (getRegSize(reg)) 
        {
            case 2: callback = (AFUNPTR) sPOP_R<16>;    break;
            case 4: callback = (AFUNPTR) sPOP_R<32>;    break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sPOP_R<64>;    break;
            #endif
            default: return;
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,    reg,            // registre destination
            IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'(E/RS)P à ce moment là
            IARG_INST_PTR, IARG_END);
    }
    else // désempilement vers mémoire
    {
        // taille de la partie de la pile lue
        switch (INS_MemoryReadSize(ins)) 
        {
            // case 1:  impossible
            case 2: callback = (AFUNPTR) sPOP_M<16>;    break;
            case 4: callback = (AFUNPTR) sPOP_M<32>;    break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sPOP_M<64>;    break;
            #endif
            default: return;
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,            // adresse réelle de lecture
            IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'(E/R)SP à ce moment là  
            IARG_INST_PTR, IARG_END);
    }
} // cPOP

void POP::cPOPF(INS &ins, UINT32 size)
{  
    void (*callback)() = nullptr; // pointeur sur la fonction à appeler
    switch (size)
    {
        case 2: callback = (AFUNPTR) sPOPF<16>; break;
        case 4: callback = (AFUNPTR) sPOPF<32>; break;
        case 8: callback = (AFUNPTR) sPOPF<64>; break;
        default: return;
    }

    // mise sur la pile de (E/R)FLAGS, selon la taille
    INS_InsertCall (ins, IPOINT_BEFORE, callback,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_STACK_PTR,  // valeur d'ESP avant le POP
        IARG_INST_PTR, IARG_END);
}

#if TARGET_IA32
void POP::cPOPA(INS &ins)
{  
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sPOPA,  
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_STACK_PTR,          // valeur d'ESP à ce moment là
        IARG_INST_PTR, IARG_END);
}

void POP::cPOPAD(INS &ins)
{ 
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sPOPAD,  
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_STACK_PTR,          // valeur d'ESP à ce moment là
        IARG_INST_PTR, IARG_END);
}

void POP::sPOPA(THREADID tid, ADDRINT spAddress, ADDRINT insAddress) 
{
    // désempilage dans l'ordre DI, SI, BP, SP (ignoré donc SP += 2), BX, DX, CX, et AX
    // du point de vue marquage, equivalent à un MOVMR sp, reg
    REG regsToPop[8] = {REG_DI, REG_SI, REG_BP, REG_SP, REG_BX, REG_DX, REG_CX, REG_AX};

    for (UINT32 tabIndex = 0; tabIndex < 8 ; ++tabIndex, spAddress += 2)
    {
        REG reg = regsToPop[tabIndex];
        
        // SP est ignoré
        if (REG_SP == reg) continue;

        // simulation du POP vers le registre
        DATAXFER::sMOV_MR<16>(tid, spAddress, reg, insAddress); 
    }
} // sPOPA

void POP::sPOPAD(THREADID tid, ADDRINT espAddress, ADDRINT insAddress) 
{
    // désempilage dans l'ordre EDI, ESI, EBP, ESP (ignoré donc SP += 4), EBX, EDX, ECX, et EAX
    // du point de vue marquage, equivalent à un MOVMR esp, reg
    REG regsToPop[8] = {REG_EDI, REG_ESI, REG_EBP, REG_ESP, REG_EBX, REG_EDX, REG_ECX, REG_EAX};

    for (UINT32 tabIndex = 0; tabIndex < 8 ; ++tabIndex, espAddress += 4)
    {
        REG reg = regsToPop[tabIndex];
        
        // ESP est ignoré
        if (REG_ESP == reg) continue;

        // simulation du POP vers le registre
        DATAXFER::sMOV_MR<32>(tid, espAddress, reg, insAddress); 
    }
} // sPOPAD
#endif
