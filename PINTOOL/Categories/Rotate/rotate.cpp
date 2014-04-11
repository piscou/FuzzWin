#include "rotate.h"

// ROTATE : traitement à l'identique de SHIFT
// Insertion de la valeur des flags dans les callbacks pour RCL/RCR

/*********/
/** ROL **/
/*********/

// CALLBACKS
void ROTATE::cROL(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : ROL_IM ou ROL_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (ROL_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sROL_IM<8>;  break;
                case 2: callback = (AFUNPTR) sROL_IM<16>; break;
                case 4: callback = (AFUNPTR) sROL_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sROL_IM<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default : return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
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
                case 8: 
                    callback = (AFUNPTR) sROL_IR<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default : return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cROL

/*********/
/** ROR **/
/*********/

// CALLBACKS
void ROTATE::cROR(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : ROR_IM ou ROR_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (ROR_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sROR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sROR_IM<16>; break;
                case 4: callback = (AFUNPTR) sROR_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sROR_IM<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
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
                case 8: 
                    callback = (AFUNPTR) sROR_IR<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cROR

/*********/
/** RCL **/
/*********/

// CALLBACKS
void ROTATE::cRCL(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : RCL_IM ou RCL_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (RCL_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sRCL_IM<8>;  break;
                case 2: callback = (AFUNPTR) sRCL_IM<16>; break;
                case 4: callback = (AFUNPTR) sRCL_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sRCL_IM<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_MEMORYWRITE_EA,  
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                CALLBACK_DEBUG IARG_END);
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
                case 8: 
                    callback = (AFUNPTR) sRCL_IR<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cRCL

/*********/
/** RCR **/
/*********/

// CALLBACKS
void ROTATE::cRCR(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : RCR_IM ou RCR_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (RCR_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sRCR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sRCR_IM<16>; break;
                case 4: callback = (AFUNPTR) sRCR_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sRCR_IM<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_MEMORYWRITE_EA,  
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                CALLBACK_DEBUG IARG_END);
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
                case 8: 
                    callback = (AFUNPTR) sRCR_IR<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID, 
                IARG_UINT32, maskedDepl,
                IARG_UINT32,    reg,    // registre décalé
                IARG_REG_VALUE, reg,    // sa valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // pour valeur du Carry Flag
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
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
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cRCR


// FLAGS 
// pour les instructions de type 'rotate' seuls OF et CF sont affectés, les autres sont inchangés

// ROL, déplacement non marqué
void ROTATE::fROL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, UINT32 maskedDepl)
{
    ObjectSource objResult(resultPtr);

    // CF/ROL = recopie du dernier bit éjecté à gauche, qui est en fait le LSB du résultat
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_LSB, objResult));
    
    // OF/ROL : ssi depl vaut 1, sinon démarquage
    if (maskedDepl == 1) pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_ROL, objResult));
    else pTmgrTls->unTaintOverflowFlag();
} // fROL

// ROL, déplacement marqué
void ROTATE::fROL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr)
{
    ObjectSource objResult(resultPtr);

    // CF/ROL = recopie du dernier bit éjecté à gauche, qui est en fait le LSB du résultat
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_LSB, objResult));
    
    // OF/ROL : démarquage si déplacement marqué (sous-marquage si la valeur est de 1...)
    pTmgrTls->unTaintOverflowFlag();
} // fROL

// ROR, déplacement non marqué
void ROTATE::fROR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, UINT32 maskedDepl)
{
    // CF/ROR = recopie du dernier bit éjecté à droite, qui est en fait le MSB du résultat
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_MSB, ObjectSource(resultPtr)));
    
    // OF/ROR : ssi depl vaut 1, sinon démarquage
    // l'opération necessite d'obtenir la source avant la rotation
    if (maskedDepl == 1)
    {
        pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_OVERFLOW_ROR, 
            resultPtr->getSources(0)));
    }
    else pTmgrTls->unTaintOverflowFlag();
} // fROR

// ROR, déplacement marqué
void ROTATE::fROR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr)
{
    // CF/ROR = recopie du dernier bit éjecté à droite, qui est en fait le MSB du résultat
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_MSB, ObjectSource(resultPtr)));
    
    // OF/ROR : démarquage si déplacement marqué (sous-marquage si la valeur est de 1...)
    pTmgrTls->unTaintOverflowFlag();
} // fROR

// RCL, déplacement non marqué
void ROTATE::fRCL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrc, UINT32 maskedDepl)
{
    // CF/RCL : recopie du dernier bit de la source ejecté à gauche (bit 'lengthInBits - depl' avec la source codée sur les bits de 0 à lengthInBits-1)
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT, 
        objSrc,
        ObjectSource(8, objSrc.getLength() - maskedDepl)));

    // Overflow Flag : mis à 1 si le signe change avant et apres rotation d'1 bit 
    if (maskedDepl == 1)
    {
        pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_OVERFLOW_RCL,
            ObjectSource(resultPtr),
            ObjectSource(pTmgrTls->getTaintCarryFlag()))); // CF apres la rotation, tout juste calculé
    }
    else pTmgrTls->unTaintOverflowFlag();
} // fRCL

// RCL, déplacement marqué
void ROTATE::fRCL(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintBytePtr &tbCountPtr)
{
    // CF/RCL : recopie du dernier bit de la source ejecté à gauche (bit 'lengthInBits - depl' avec la source codée sur les bits de 0 à lengthInBits-1)
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        F_CARRY_RCL, 
        objSrc,
        ObjectSource(tbCountPtr)));

    // OF/RCL : démarquage si déplacement marqué (sous-marquage si la valeur est de 1...)
    pTmgrTls->unTaintOverflowFlag();
} // fRCL


// RCR, déplacement non marqué
void ROTATE::fRCR(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const ObjectSource &objCarryFlagBeforeRcr, UINT32 maskedDepl)
{
    // CF/RCR : recopie du dernier bit de la source ejecté à droite (bit 'depl - 1' avec la source codée sur les bits de 0 à lengthInBits-1)
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT, 
        objSrc,
        ObjectSource(8, maskedDepl - 1)));

    // OF/RCR (slt si depl de 1): mis à 1 si le signe change avant et apres rotation d'1 bit 
    if (maskedDepl == 1)
    {
        pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_OVERFLOW_RCR,
            objSrc,
            objCarryFlagBeforeRcr)); // CF apres la rotation, tout juste calculé
    }
    else pTmgrTls->unTaintOverflowFlag();
} // fRCL

// RCR, déplacement marqué
void ROTATE::fRCR(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintBytePtr &tbCountPtr)
{
    // CF/RCR : recopie du dernier bit de la source ejecté à droite (bit 'depl - 1' avec la source codée sur les bits de 0 à lengthInBits-1)
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        F_CARRY_RCR, 
        objSrc,
        ObjectSource(tbCountPtr)));

    // OF/RCR : démarquage si déplacement marqué (sous-marquage si la valeur est de 1...)
    pTmgrTls->unTaintOverflowFlag();
} // fRCL

// démarquage flags ROTATE : uniquement OF et CF
void ROTATE::fUnTaintROTATE(TaintManager_Thread *pTmgrTls)
{
    pTmgrTls->unTaintCarryFlag();
    pTmgrTls->unTaintOverflowFlag();
}
