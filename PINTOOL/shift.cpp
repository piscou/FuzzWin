#include "SHIFT.h"

// FLAGS
// cas particuliers par rapport au manuel Intel : 
// pour AF : "undefined" selon Intel => démarquage dans FuzzWin
// pour OF : "undefined" si déplacement != 1 => démarquage dans FuzzWin

// démarquage OZSAP
void SHIFT::fUnTaintOZSAP(TaintManager_Thread *pTmgrTls)
{
    pTmgrTls->unTaintParityFlag(); 
    pTmgrTls->unTaintZeroFlag();
    pTmgrTls->unTaintSignFlag();  
    pTmgrTls->unTaintOverflowFlag(); 
    pTmgrTls->unTaintAuxiliaryFlag();
}

// Les instructions SHIFT sont traitées de manière très précise, afin
// de limiter les faux-positifs en marquage.
// deux cas sont distingués : déplacement par valeur ou par registre (CL)
// si CL n'est pas marqué, l'instruction sera traitée comme un déplacement par valeur

// plusieurs cas sont envisagés
// déplacement numérique nul => aucune action
// deplacement numérique = 1 => cas spécifique marquage OF en plus
// déplacement numérique multiple de 8 => traitement par MOV octet par octet
// déplacement numérique supérieur à la taille destination => démarquage
// 
// si déplacement avec CL marqué, on ne pourra pas faire d'optimisations
// il y aura possibilité de surmarquage selon la valeur réelle de CL

// chaque procédure d'analyse SHIFT sera découpée en plusieurs parties
// 0) (instrumentation) masquage du déplacement à 0x1f ou 0x3f selon archi
// 1) (analyse) test du marquage des opérandes (registre ET décalage)
// 2) Marquage destination avec SHL/SHR/SAR
// 3) Procédure marquage flags selon instruction SHL/SHR/SAR
// 4) démarquage de certaines parties de la destination, en fonction de 
//    la valeur du déplacement et de la taille du registre (uniquement pour
//    les déplacements numériques)

/*********/
/** SHL **/
/*********/

// CALLBACKS
void SHIFT::cSHL(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : SHL_IM ou SHL_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHL_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sSHL_IM<8>;  break;
                case 2: callback = (AFUNPTR) sSHL_IM<16>; break;
                case 4: callback = (AFUNPTR) sSHL_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHL_IM<64>; 
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
        else // DESTINATION = REGISTRE (SHL_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sSHL_IR<8>;  break;
                case 2: callback = (AFUNPTR) sSHL_IR<16>; break;
                case 4: callback = (AFUNPTR) sSHL_IR<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHL_IR<64>; 
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
    // DECALAGE PAR REGISTRE : SHL_RM ou SHL_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f du registre sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHL_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sSHL_RM<8>;  break;
                case 2: callback = (AFUNPTR) sSHL_RM<16>; break;
                case 4: callback = (AFUNPTR) sSHL_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHL_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SHL_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sSHL_RR<8>;  break;
                case 2: callback = (AFUNPTR) sSHL_RR<16>; break;
                case 4: callback = (AFUNPTR) sSHL_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHL_RR<64>; break;
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
} // cSHL

/** FLAGS **/
// marquage flags spécifique pour SHL, déplacement non marqué
void SHIFT::fSHL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel)
    pTmgrTls->unTaintAuxiliaryFlag();
    // marquage ZF et SF
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB,     objResult));

    // marquage Carry : bit (length-depl) de la source
    // peut quand meme provoquer un surmarquage si l'octet concerné n'est pas marqué
    // mais le test de marquage serait trop gourmand en temps d'execution
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT,
        objSrcShiftedSrc,
        ObjectSource(8, resultPtr->getLength() - maskedDepl)));

    // marquage PF ssi deplacement inférieur à 8 (sinon que des 0)
    if (maskedDepl < 8)  pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    else pTmgrTls->unTaintParityFlag();

    // marquage Overflow, ssi depl = 1
    if (maskedDepl == 1)  pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_OVERFLOW_SHL,
            objResult,
            objSrcShiftedSrc));
    else pTmgrTls->unTaintOverflowFlag();
} // fSHL

// marquage flags spécifique pour SHL, déplacement marqué
void SHIFT::fSHL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel)
    pTmgrTls->unTaintAuxiliaryFlag();
    // marquage ZF et SF
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB,     objResult));

    // marquage PF 
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
        
    // marquage Carry : dernier bit de la source éjecté suite au shift       
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        F_CARRY_SHL,
        objSrcShiftedSrc,
        objTbCount));

    // démarquage Overflow (tant pis si le déplacement vaut 1...il y aura sous marquage)
    pTmgrTls->unTaintOverflowFlag();
} // fSHL

/*********/
/** SHR **/
/*********/

// CALLBACKS
void SHIFT::cSHR(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : SHR_IM ou SHR_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement par défaut à 0x1f
        // sera modifié par la suite si opérande 64bits 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHR_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sSHR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sSHR_IM<16>; break;
                case 4: callback = (AFUNPTR) sSHR_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHR_IM<64>; 
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
        else // DESTINATION = REGISTRE (SHR_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sSHR_IR<8>;  break;
                case 2: callback = (AFUNPTR) sSHR_IR<16>; break;
                case 4: callback = (AFUNPTR) sSHR_IR<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHR_IR<64>; 
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
    // DECALAGE PAR REGISTRE : SHR_RM ou SHR_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f du registre sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHR_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sSHR_RM<8>;  break;
                case 2: callback = (AFUNPTR) sSHR_RM<16>; break;
                case 4: callback = (AFUNPTR) sSHR_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHR_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SHR_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sSHR_RR<8>;  break;
                case 2: callback = (AFUNPTR) sSHR_RR<16>; break;
                case 4: callback = (AFUNPTR) sSHR_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHR_RR<64>; break;
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
} // cSHR

/** FLAGS **/
// marquage flags spécifique pour SHR, déplacement non marqué
void SHIFT::fSHR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel) et SF (puisque insertion zéros)
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintSignFlag();

    // marquage ZF et PF
    pTmgrTls->updateTaintZeroFlag  (std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    
    // marquage Carry : bit (depl - 1) de la source
    // peut provoquer un surmarquage si l'octet concerné n'est pas marqué
    // mais le test de marquage serait trop gourmand en temps d'execution
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT,
        objSrcShiftedSrc,
        ObjectSource(8, maskedDepl - 1)));

    // marquage Overflow, ssi depl = 1 POUR SHR, OF vaut le bit de poids fort de la source (cf manuel Intel)
    if (maskedDepl == 1)  pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_MSB,
            objSrcShiftedSrc));
    else pTmgrTls->unTaintOverflowFlag();
} // fSHR

// marquage flags spécifique pour SHR, déplacement marqué
void SHIFT::fSHR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel) et SF (puisque insertion zéros)
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintSignFlag();

    // marquage ZF et PF
    pTmgrTls->updateTaintZeroFlag  (std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    
    // marquage Carry : dernier bit de la source éjecté suite au shift       
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        F_CARRY_SHR,
        objSrcShiftedSrc,
        objTbCount));

    // démarquage Overflow (tant pis si le déplacement vaut 1...il y aura sous marquage)
    pTmgrTls->unTaintOverflowFlag();
} // fSHR

/*********/
/** SAR **/
/*********/

// CALLBACKS
void SHIFT::cSAR(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    
    // DECALAGE PAR VALEUR : SAR_IM ou SAR_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement par défaut à 0x1f
        // sera modifié par la suite si opérande 64bits 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SAR_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sSAR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sSAR_IM<16>; break;
                case 4: callback = (AFUNPTR) sSAR_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSAR_IM<64>; 
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
        else // DESTINATION = REGISTRE (SAR_IR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sSAR_IR<8>;  break;
                case 2: callback = (AFUNPTR) sSAR_IR<16>; break;
                case 4: callback = (AFUNPTR) sSAR_IR<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSAR_IR<64>; 
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
    // DECALAGE PAR REGISTRE : SAR_RM ou SAR_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SAR_RM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                case 1: callback = (AFUNPTR) sSAR_RM<8>;  break;
                case 2: callback = (AFUNPTR) sSAR_RM<16>; break;
                case 4: callback = (AFUNPTR) sSAR_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSAR_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SAR_RR)
        {         
            REG reg = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(reg)) 
            {
                case 1: callback = (AFUNPTR) sSAR_RR<8>;  break;
                case 2: callback = (AFUNPTR) sSAR_RR<16>; break;
                case 4: callback = (AFUNPTR) sSAR_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSAR_RR<64>; break;
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
} // cSAR

/** FLAGS **/
// marquage flags spécifique pour SAR, déplacement non marqué
void SHIFT::fSAR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl) 
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel) et OF (spécifique SAR) 
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintOverflowFlag();

    // marquage SF avec le signe de la source
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objSrcShiftedSrc));

    // marquage ZF et PF
    pTmgrTls->updateTaintZeroFlag  (std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    
    // marquage Carry : bit (depl - 1) de la source
    // peut provoquer un surmarquage si l'octet concerné n'est pas marqué
    // mais le test de marquage serait trop gourmand en temps d'execution
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT,
        objSrcShiftedSrc,
        ObjectSource(8, maskedDepl - 1))); 
} // fSAR 

// marquage flags spécifique pour SAR, déplacement marqué
void SHIFT::fSAR(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount) 
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel) et OF (spécifique SAR) 
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintOverflowFlag();

    // marquage SF avec le signe de la source
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objSrcShiftedSrc));

    // marquage ZF et PF
    pTmgrTls->updateTaintZeroFlag  (std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    
    // marquage Carry : dernier bit de la source éjecté suite au shift       
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        F_CARRY_SAR,
        objSrcShiftedSrc,
        objTbCount));
} // fSAR 

/**********/
/** SHLD **/
/**********/

// CALLBACKS
void SHIFT::cSHLD(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    REG regSrc = INS_OperandReg(ins, 1); // registre "source" (2eme opérande, tjs registre)
    UINT32 regSrcSize = getRegSize(regSrc);
    if (!regSrc) return;    // registre non supporté

    // DECALAGE PAR VALEUR : SHLD_IM ou SHLD_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHLD_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHLD_IM<16>; break;
                case 4: callback = (AFUNPTR) sSHLD_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHLD_IM<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, maskedDepl,
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SHLD_IR)
        {         
            REG regDest = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(regDest)) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHLD_IR<16>; break;
                case 4: callback = (AFUNPTR) sSHLD_IR<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHLD_IR<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, maskedDepl,
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_UINT32,    regDest,    // registre décalé
                IARG_REG_VALUE, regDest,    // sa valeur lors du callback
                CALLBACK_DEBUG IARG_END);
        }
    }
    // DECALAGE PAR REGISTRE : SHLD_RM ou SHLD_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHLD_RM)
        {   
            switch (regSrcSize) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHLD_RM<16>; break;
                case 4: callback = (AFUNPTR) sSHLD_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHLD_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SHLD_RR)
        {         
            REG regDest = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(regDest)) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHLD_RR<16>; break;
                case 4: callback = (AFUNPTR) sSHLD_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHLD_RR<64>; break;
                #endif
                default: return;
            }   
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_UINT32,    regDest,    // registre décalé
                IARG_REG_VALUE, regDest,    // sa valeur lors du callback
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cSHLD

/** FLAGS **/
// marquage flags spécifique pour SHLD, déplacement non marqué
void SHIFT::fSHLD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          UINT32 maskedDepl)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel)
    pTmgrTls->unTaintAuxiliaryFlag();
    // marquage ZF et SF
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB,     objResult));
    // marquage PF dans tous les cas (contrairement à SHL ou on le faisait si depl < 8)
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));

    // marquage Carry : bit (length-depl) de la source
    // peut quand meme provoquer un surmarquage si l'octet concerné n'est pas marqué
    // mais le test de marquage serait trop gourmand en temps d'execution
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT,
        objSrcShiftedSrc,
        ObjectSource(8, resultPtr->getLength() - maskedDepl)));

    // marquage Overflow, ssi depl = 1
    if (maskedDepl == 1)  pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_OVERFLOW_SHL,
            objResult,
            objSrcShiftedSrc));
    else pTmgrTls->unTaintOverflowFlag();
} // fSHLD

// marquage flags spécifique pour SHLD, déplacement marqué
void SHIFT::fSHLD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objSrcShiftedSrc,
          const ObjectSource &objTbCount)
{
    // pour le cas 'deplacement marqué', flags identiques à SHL
    fSHL(pTmgrTls, resultPtr, objSrcShiftedSrc, objTbCount);
} // fSHLD

/**********/
/** SHRD **/
/**********/

void SHIFT::cSHRD(INS &ins) 
{
    void (*callback)() = nullptr;     // pointeur sur la fonction a appeler
    REG regSrc = INS_OperandReg(ins, 1); // registre "source" (2eme opérande, tjs registre)
    UINT32 regSrcSize = getRegSize(regSrc);
    if (!regSrc) return;    // registre non supporté

    // DECALAGE PAR VALEUR : SHRD_IM ou SHRD_IR
    if (INS_OperandIsImmediate(ins, 1)) 
    {    
        // masquage du déplacement à 0x1f (meme en x64), sauf si opérande 64bits (masquage à 0x3f) 
        UINT32 depl = static_cast<UINT32>(INS_OperandImmediate(ins, 1));
        UINT32 maskedDepl = depl & 0x1f;   
        
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHRD_IM)
        {   
            switch (INS_MemoryWriteSize(ins)) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHRD_IM<16>; break;
                case 4: callback = (AFUNPTR) sSHRD_IM<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHRD_IM<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, maskedDepl,
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SHRD_IR)
        {         
            REG regDest = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(regDest)) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHRD_IR<16>; break;
                case 4: callback = (AFUNPTR) sSHRD_IR<32>; break;
                #if TARGET_IA32E
                case 8: 
                    callback = (AFUNPTR) sSHRD_IR<64>; 
                    maskedDepl = depl & 0x3f;   // masquage à 0x3f en 64bits
                    break;
                #endif
                default: return;
            } 
            
            // déplacement non nul : instrumentation (sinon aucun chgt)
            if (maskedDepl) INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, maskedDepl,
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_UINT32,    regDest,    // registre décalé
                IARG_REG_VALUE, regDest,    // sa valeur lors du callback
                CALLBACK_DEBUG IARG_END);
        }
    }
    // DECALAGE PAR REGISTRE : SHRD_RM ou SHRD_RR
    else 
    {  
        // le masquage à 0x1f ou 0x3f sera fait dans le callback
        if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE (SHRD_RM)
        {   
            switch (regSrcSize) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHRD_RM<16>; break;
                case 4: callback = (AFUNPTR) sSHRD_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHRD_RM<64>; break;
                #endif
                default: return;
            } 
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,   
                CALLBACK_DEBUG IARG_END);
        }
        else // DESTINATION = REGISTRE (SHRD_RR)
        {         
            REG regDest = INS_OperandReg(ins, 0); // registre qui sera décalé 
            switch (getRegSize(regDest)) 
            {
                // case 1: impossible
                case 2: callback = (AFUNPTR) sSHRD_RR<16>; break;
                case 4: callback = (AFUNPTR) sSHRD_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSHRD_RR<64>; break;
                #endif
                default: return;
            }   
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_REG_VALUE, REG_CL, // valeur numérique du déplacement
                IARG_UINT32, regSrc,
                IARG_REG_VALUE, regSrc,
                IARG_UINT32,    regDest,    // registre décalé
                IARG_REG_VALUE, regDest,    // sa valeur lors du callback
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cSHRD

/** FLAGS **/
// marquage flags spécifique pour SHRD, déplacement non marqué
void SHIFT::fSHRD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objConcatenatedSrc,
          UINT32 maskedDepl)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel) et SF (puisque insertion zéros)
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintSignFlag();

    // marquage ZF et PF
    pTmgrTls->updateTaintZeroFlag  (std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    
    // marquage Carry : bit (depl - 1) de la source, (PEU IMPORTE QU'ELLE SOIT ICI CONCATENEE)
    // peut provoquer un surmarquage si l'octet concerné n'est pas marqué
    // mais le test de marquage serait trop gourmand en temps d'execution
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        EXTRACT,
        objConcatenatedSrc,
        ObjectSource(8, maskedDepl - 1)));

    // marquage Overflow, ssi depl = 1 
    // POUR SHRD, OF vaut 1 si changement de signe, donc si MSB srcDest != LSB BitPattern
    if (maskedDepl == 1)  pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            F_OVERFLOW_SHRD,
            objConcatenatedSrc));
    else pTmgrTls->unTaintOverflowFlag();
} // fSHRD

// marquage flags spécifique pour SHRD, déplacement marqué
void SHIFT::fSHRD(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr, const ObjectSource &objConcatenatedSrc,
          const ObjectSource &objTbCount)
{
    ObjectSource objResult(resultPtr);
    
    // démarquage AF (undefined selon Intel) et SF (puisque insertion zéros)
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintSignFlag();

    // marquage ZF et PF
    pTmgrTls->updateTaintZeroFlag  (std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    
    // marquage Carry : dernier bit de la source éjecté suite au shift       
    pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
        F_CARRY_SHR,
        objConcatenatedSrc,
        objTbCount));

    // POUR SHRD, OF vaut 1 si changement de signe, donc si MSB srcDest != LSB BitPattern
    // probable surmarquage car OF marqué ssi depl == 1; solution : démarquer !!!
    pTmgrTls->unTaintOverflowFlag();
} // fSHRD

