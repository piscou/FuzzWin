#include "rotate.h"

// ROTATE : traitement similaire à SHIFT
// Insertion de la valeur des flags dans les callbacks pour RCL/RCR

/** ROL **/
void ROTATE::cROL(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : ROL_IM ou ROL_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1)); 
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (ROL_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sROL_IM<8>;  break;
                case 2: callback = (AFUNPTR) sROL_IM<16>; break;
                case 4: callback = (AFUNPTR) sROL_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROL_IM<64>; break;
                #endif
                default : return;
            } 
            // instrumentation meme si déplacement null (CF impacté)
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, depl,
                IARG_MEMORYWRITE_EA,   
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (ROL_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sROL_IR<8>;  break;
                case 2: callback = (AFUNPTR) sROL_IR<16>; break;
                case 4: callback = (AFUNPTR) sROL_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROL_IR<64>; break;
                #endif
                default : return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32,    depl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
    }
    // DECALAGE PAR REGISTRE : ROL_RM ou ROL_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (ROL_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sROL_RM<8>;  break;
                case 2: callback = (AFUNPTR) sROL_RM<16>; break;
                case 4: callback = (AFUNPTR) sROL_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROL_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA,   
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (ROL_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sROL_RR<8>;  break;
                case 2: callback = (AFUNPTR) sROL_RR<16>; break;
                case 4: callback = (AFUNPTR) sROL_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROL_RR<64>; break;
                #endif
                default: return;
            } 
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
    }
} // cROL

/** ROR **/
void ROTATE::cROR(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : ROR_IM ou ROR_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));

        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (ROR_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sROR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sROR_IM<16>; break;
                case 4: callback = (AFUNPTR) sROR_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROR_IM<64>; break;
                #endif
                default: return;
            } 

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, depl,
                IARG_MEMORYWRITE_EA,   
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (ROR_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sROR_IR<8>;  break;
                case 2: callback = (AFUNPTR) sROR_IR<16>; break;
                case 4: callback = (AFUNPTR) sROR_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROR_IR<64>; break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32,    depl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
    }
    // DECALAGE PAR REGISTRE : ROR_RM ou ROR_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (ROR_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sROR_RM<8>;  break;
                case 2: callback = (AFUNPTR) sROR_RM<16>; break;
                case 4: callback = (AFUNPTR) sROR_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROR_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA,   
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (ROR_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sROR_RR<8>;  break;
                case 2: callback = (AFUNPTR) sROR_RR<16>; break;
                case 4: callback = (AFUNPTR) sROR_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sROR_RR<64>; break;
                #endif
                default: return;
            } 
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
    }
} // cROR

/** RCL **/
void ROTATE::cRCL(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : RCL_IM ou RCL_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));

        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (RCL_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sRCL_IM<8>;  break;
                case 2: callback = (AFUNPTR) sRCL_IM<16>; break;
                case 4: callback = (AFUNPTR) sRCL_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCL_IM<64>; break;
                #endif
                default: return;
            } 

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, depl,
                IARG_MEMORYWRITE_EA,  
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (RCL_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sRCL_IR<8>;  break;
                case 2: callback = (AFUNPTR) sRCL_IR<16>; break;
                case 4: callback = (AFUNPTR) sRCL_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCL_IR<64>; break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32,    depl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
    }
    // DECALAGE PAR REGISTRE : RCL_RM ou RCL_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (RCL_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sRCL_RM<8>;  break;
                case 2: callback = (AFUNPTR) sRCL_RM<16>; break;
                case 4: callback = (AFUNPTR) sRCL_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCL_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA, 
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (RCL_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sRCL_RR<8>;  break;
                case 2: callback = (AFUNPTR) sRCL_RR<16>; break;
                case 4: callback = (AFUNPTR) sRCL_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCL_RR<64>; break;
                #endif
                default: return;
            } 
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
    }
} // cRCL

/** RCR **/
void ROTATE::cRCR(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : RCR_IM ou RCR_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));  
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (RCR_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sRCR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sRCR_IM<16>; break;
                case 4: callback = (AFUNPTR) sRCR_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCR_IM<64>; break;
                #endif
                default: return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, depl,
                IARG_MEMORYWRITE_EA,  
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (RCR_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sRCR_IR<8>;  break;
                case 2: callback = (AFUNPTR) sRCR_IR<16>; break;
                case 4: callback = (AFUNPTR) sRCR_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCR_IR<64>; break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32,    depl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
    }
    // DECALAGE PAR REGISTRE : RCR_RM ou RCR_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (RCR_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sRCR_RM<8>;  break;
                case 2: callback = (AFUNPTR) sRCR_RM<16>; break;
                case 4: callback = (AFUNPTR) sRCR_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCR_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA, 
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
        else // DESTINATION = REGISTRE (RCR_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sRCR_RR<8>;  break;
                case 2: callback = (AFUNPTR) sRCR_RR<16>; break;
                case 4: callback = (AFUNPTR) sRCR_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sRCR_RR<64>; break;
                #endif
                default: return;
            } 
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                IARG_INST_PTR, IARG_END);
        }
    }
} // cRCR
