#include "binary.h"
#include <Translate\translate.h> // pour ajout des contraintes sur DIV/IDIV

/////////
// NEG //
/////////

// CALLBACKS
void BINARY::cNEG(INS &ins) 
{ 
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE => NEGM
    {	
        switch (INS_MemoryWriteSize(ins)) // taille de l'opérande mémoire
        {	
            case 1:	callback = (AFUNPTR) sNEG_M<8>;	break;
            case 2:	callback = (AFUNPTR) sNEG_M<16>;break;
            case 4:	callback = (AFUNPTR) sNEG_M<32>;break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sNEG_M<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,
            IARG_INST_PTR, IARG_END);
    } 
    else // NEGR
    {                                  
        REG reg = INS_OperandReg(ins, 0);
        switch (getRegSize(reg)) 
        {
            case 1:	callback = (AFUNPTR) sNEG_R<8>;	break;
            case 2:	callback = (AFUNPTR) sNEG_R<16>;break;
            case 4:	callback = (AFUNPTR) sNEG_R<32>;break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sNEG_R<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,	reg,	// registre source
            IARG_REG_VALUE, reg,	// sa valeur lors du callback
            IARG_INST_PTR, IARG_END);
    }
}

// FLAGS
void BINARY::fTaintNEG(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintPtr &resultPtr) 
{
    ObjectSource objResult(resultPtr);
 
    // NEG : O/S/Z/A/P/C
    pTmgrTls->updateTaintCarryFlag (std::make_shared<TaintBit>(F_CARRY_NEG, objSrc));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AUXILIARY_NEG, objSrc));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objSrc));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objResult));
    pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_NEG, objSrc));
} // fTaintNEG

/////////
// INC //
/////////

// CALLBACKS
void BINARY::cINC(INS &ins) 
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        switch (INS_MemoryWriteSize(ins)) // taille de l'opérande mémoire
        {	
            case 1:	callback = (AFUNPTR) sINC_M<8>;	 break;
            case 2:	callback = (AFUNPTR) sINC_M<16>; break;
            case 4:	callback = (AFUNPTR) sINC_M<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sINC_M<64>; break;
            #endif 
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,
            IARG_INST_PTR, IARG_END);
    } 
    else // INCR
    {                                  
        REG reg  = INS_OperandReg(ins, 0);
        switch (getRegSize(reg)) 
        {
            case 1:	callback = (AFUNPTR) sINC_R<8>;	 break;
            case 2:	callback = (AFUNPTR) sINC_R<16>; break;
            case 4:	callback = (AFUNPTR) sINC_R<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sINC_R<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,	reg,	// registre source
            IARG_REG_VALUE, reg,	// sa valeur lors du callback
            IARG_INST_PTR, IARG_END);
    }
} // cINC

// FLAGS
void BINARY::fTaintINC
    (TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintPtr &resultPtr) 
{
    ObjectSource objResult(resultPtr);
 
    // INC : O/S/Z/A/P	
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AUXILIARY_INC, objSrc));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objResult));
    pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_INC, objSrc));

} // fTaintINC

// procédure commune INC/DEC
void BINARY::fUnTaintINCDEC(TaintManager_Thread *pTmgrTls)
{
    // le CF n'est pas affecté par INC ni DEC
    pTmgrTls->unTaintParityFlag();
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintZeroFlag();
    pTmgrTls->unTaintSignFlag();
    pTmgrTls->unTaintOverflowFlag();
} // fUnTaintINCDEC

/////////
// DEC //
/////////

// CALLBACKS
void BINARY::cDEC(INS &ins) 
{ 
    void (*callback)() = nullptr;	// pointeur sur la fonction générique à appeler

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        switch (INS_MemoryWriteSize(ins)) // taille de l'opérande mémoire
        {	
            case 1:	callback = (AFUNPTR) sDEC_M<8>;  break;
            case 2:	callback = (AFUNPTR) sDEC_M<16>; break;
            case 4:	callback = (AFUNPTR) sDEC_M<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sDEC_M<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYWRITE_EA,
            IARG_INST_PTR, IARG_END);
    } 
    else  // DECR
    {                                 
        REG reg  = INS_OperandReg(ins, 0);
        switch (getRegSize(reg))
        {
            case 1:	callback = (AFUNPTR) sDEC_R<8>;	 break;
            case 2:	callback = (AFUNPTR) sDEC_R<16>; break;
            case 4:	callback = (AFUNPTR) sDEC_R<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sDEC_R<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,	reg,	// registre source
            IARG_REG_VALUE, reg,	// sa valeur lors du callback
            IARG_INST_PTR, IARG_END);
    }
} // cDEC

// FLAGS
void BINARY::fTaintDEC(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrc, const TaintPtr &resultPtr) 
{
    ObjectSource objResult(resultPtr);
 
    // DEC : O/S/Z/A/P	
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AUXILIARY_DEC, objSrc));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objResult));
    pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_DEC, objSrc));
} // fTaintDEC

/////////
// ADC //
/////////

// CALLBACKS
void BINARY::cADC(INS &ins) 
{ 	
    void (*callback)() = nullptr;	
    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        UINT32 writeSize = INS_MemoryWriteSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // ADC_IM
        {	
            switch (writeSize) // taille de l'opérande mémoire
            {	
                case 1:	callback = (AFUNPTR) sADC_IM<8>;  break;
                case 2:	callback = (AFUNPTR) sADC_IM<16>; break;
                case 4:	callback = (AFUNPTR) sADC_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADC_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        } 
        else // ADC_RM
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sADC_RM<8>;  break;
                case 2:	callback = (AFUNPTR) sADC_RM<16>; break;
                case 4:	callback = (AFUNPTR) sADC_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADC_RM<64>; break;
                #endif
                default: return; // normalement il faudrait démarquer la mémoire...
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc, 
                IARG_MEMORYWRITE_EA, 
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest  = INS_OperandReg(ins, 0);
        UINT32 regSize = getRegSize(regDest);
        if (!regSize) return;	        // registre non géré
        else if (INS_IsMemoryRead(ins)) // ADC_MR
        {			
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sADC_MR<8>;  break;
                case 2:	callback = (AFUNPTR) sADC_MR<16>; break;
                case 4:	callback = (AFUNPTR) sADC_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADC_MR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		    // adresse réelle de lecture
                IARG_UINT32, regDest,	    // registre destination
                IARG_REG_VALUE, regDest,    // valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1))  // ADC_IR
        {         
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sADC_IR<8>; break;
                case 2:	callback = (AFUNPTR) sADC_IR<16>; break;
                case 4:	callback = (AFUNPTR) sADC_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADC_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest,	    // registre destination
                IARG_REG_VALUE, regDest,    // valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }
        else // ADC_RR
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sADC_RR<8>;  break;
                case 2:	callback = (AFUNPTR) sADC_RR<16>; break;
                case 4:	callback = (AFUNPTR) sADC_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADC_RR<64>; break;
                #endif
                default: return; // registre source non suivi
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc,		// registre source
                IARG_REG_VALUE, regSrc,		// valeur lors du callback
                IARG_UINT32,    regDest,	// registre de destination
                IARG_REG_VALUE, regDest,	// valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }  
    }
} // cADC

/////////
// ADD //
/////////

// CALLBACKS
void BINARY::cADD(INS &ins) 
{ 	
    void (*callback)() = nullptr;	
    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        UINT32 writeSize = INS_MemoryWriteSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // ADDIM
        {	
            switch (writeSize) // taille de l'opérande mémoire
            {	
                case 1:	callback = (AFUNPTR) sADD_IM<8>;  break;
                case 2:	callback = (AFUNPTR) sADD_IM<16>; break;
                case 4:	callback = (AFUNPTR) sADD_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADD_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                IARG_INST_PTR, IARG_END);
        } 
        else // ADDRM
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sADD_RM<8>;  break;
                case 2:	callback = (AFUNPTR) sADD_RM<16>; break;
                case 4:	callback = (AFUNPTR) sADD_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADD_RM<64>; break;
                #endif
                default: return;    // normalement il faudrait démarquer la mémoire...
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc, 
                IARG_MEMORYWRITE_EA, 
                IARG_INST_PTR, IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest  = INS_OperandReg(ins, 0);
        UINT32 regSize = getRegSize(regDest);
        if (!regSize) return;	   // registre non géré
        else if (INS_IsMemoryRead(ins)) // ADDMR
        {			
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sADD_MR<8>;  break;
                case 2:	callback = (AFUNPTR) sADD_MR<16>; break;
                case 4:	callback = (AFUNPTR) sADD_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADD_MR<64>; break;
                #endif
                default: return;
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		// adresse réelle de lecture
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1))  // ADDIR
        {         
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sADD_IR<8>; break;
                case 2:	callback = (AFUNPTR) sADD_IR<16>; break;
                case 4:	callback = (AFUNPTR) sADD_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADD_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else // ADDRR
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sADD_RR<8>;  break;
                case 2:	callback = (AFUNPTR) sADD_RR<16>; break;
                case 4:	callback = (AFUNPTR) sADD_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sADD_RR<64>; break;
                #endif
                default: return; // registre source non suivi
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc,		// registre source
                IARG_REG_VALUE, regSrc,		// valeur lors du callback
                IARG_UINT32,    regDest,	// registre de destination
                IARG_REG_VALUE, regDest,	// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }  
    }
} // cADD

// FLAGS
void BINARY::fTaintADD
    (TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, const ObjectSource &objSrc, const TaintPtr &resultPtr)
{
    ObjectSource objResult(resultPtr);
    
    // ADD : O/S/Z/A/P/C
    pTmgrTls->updateTaintCarryFlag (std::make_shared<TaintBit>(F_CARRY_ADD, objSrcDest, objSrc));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AUXILIARY_ADD, objSrcDest, objSrc));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objResult));
    pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_ADD, objSrcDest, objSrc, objResult));
} // fTaintADD


/////////
// SBB //
/////////

// CALLBACKS
void BINARY::cSBB(INS &ins) 
{ 	
    void (*callback)() = nullptr;	
    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        UINT32 writeSize = INS_MemoryWriteSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // SBB_IM
        {	
            switch (writeSize) // taille de l'opérande mémoire
            {	
                case 1:	callback = (AFUNPTR) sSBB_IM<8>;  break;
                case 2:	callback = (AFUNPTR) sSBB_IM<16>; break;
                case 4:	callback = (AFUNPTR) sSBB_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSBB_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        } 
        else // SBB_RM
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sSBB_RM<8>;  break;
                case 2:	callback = (AFUNPTR) sSBB_RM<16>; break;
                case 4:	callback = (AFUNPTR) sSBB_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSBB_RM<64>; break;
                #endif
                default: return; // normalement il faudrait démarquer la mémoire...
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc, 
                IARG_MEMORYWRITE_EA, 
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest  = INS_OperandReg(ins, 0);
        UINT32 regSize = getRegSize(regDest);
        if (!regSize) return;	        // registre non géré
        else if (INS_IsMemoryRead(ins)) // SBB_MR
        {			
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sSBB_MR<8>;  break;
                case 2:	callback = (AFUNPTR) sSBB_MR<16>; break;
                case 4:	callback = (AFUNPTR) sSBB_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSBB_MR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		    // adresse réelle de lecture
                IARG_UINT32, regDest,	    // registre destination
                IARG_REG_VALUE, regDest,    // valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1))  // SBB_IR
        {         
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sSBB_IR<8>; break;
                case 2:	callback = (AFUNPTR) sSBB_IR<16>; break;
                case 4:	callback = (AFUNPTR) sSBB_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSBB_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest,	    // registre destination
                IARG_REG_VALUE, regDest,    // valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }
        else // SBB_RR
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sSBB_RR<8>;  break;
                case 2:	callback = (AFUNPTR) sSBB_RR<16>; break;
                case 4:	callback = (AFUNPTR) sSBB_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSBB_RR<64>; break;
                #endif
                default: return; // registre source non suivi
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc,		// registre source
                IARG_REG_VALUE, regSrc,		// valeur lors du callback
                IARG_UINT32,    regDest,	// registre de destination
                IARG_REG_VALUE, regDest,	// valeur lors du callback
                IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (pour CF)
                IARG_INST_PTR, IARG_END);
        }  
    }
} // cSBB


/////////
// SUB //
/////////

// CALLBACKS
void BINARY::cSUB(INS &ins) 
{ 	
    void (*callback)() = nullptr;	
    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        UINT32 writeSize = INS_MemoryWriteSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // SUBIM
        {	
            switch (writeSize) // taille de l'opérande mémoire
            {	
                case 1:	callback = (AFUNPTR) sSUB_IM<8>;  break;
                case 2:	callback = (AFUNPTR) sSUB_IM<16>; break;
                case 4:	callback = (AFUNPTR) sSUB_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSUB_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                IARG_INST_PTR, IARG_END);
        } 
        else // SUBRM
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sSUB_RM<8>;  break;
                case 2:	callback = (AFUNPTR) sSUB_RM<16>; break;
                case 4:	callback = (AFUNPTR) sSUB_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSUB_RM<64>; break;
                #endif
                default: return;    // normalement il faudrait démarquer la mémoire...
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc, 
                IARG_MEMORYWRITE_EA, 
                IARG_INST_PTR, IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest  = INS_OperandReg(ins, 0);
        UINT32 regSize = getRegSize(regDest);
        if (!regSize) return;	   // registre non géré
        else if (INS_IsMemoryRead(ins)) // SUBMR
        {			
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sSUB_MR<8>;  break;
                case 2:	callback = (AFUNPTR) sSUB_MR<16>; break;
                case 4:	callback = (AFUNPTR) sSUB_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSUB_MR<64>; break;
                #endif
                default: return;
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		// adresse réelle de lecture
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1))  // SUBIR
        {         
            switch (regSize) 
            {	
                case 1:	callback = (AFUNPTR) sSUB_IR<8>; break;
                case 2:	callback = (AFUNPTR) sSUB_IR<16>; break;
                case 4:	callback = (AFUNPTR) sSUB_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSUB_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else // SUBRR
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sSUB_RR<8>;  break;
                case 2:	callback = (AFUNPTR) sSUB_RR<16>; break;
                case 4:	callback = (AFUNPTR) sSUB_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sSUB_RR<64>; break;
                #endif
                default: return; // registre source non suivi
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc,		// registre source
                IARG_REG_VALUE, regSrc,		// valeur lors du callback
                IARG_UINT32, regDest,		// registre de destination
                IARG_REG_VALUE, regDest,	// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }  
    }
} // cSUB

// FLAGS 
void BINARY::fTaintSUB
    (TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, const ObjectSource &objSrc, const TaintPtr &resultPtr) 
{
    ObjectSource objResult(resultPtr);
    
    // SUB : O/S/Z/A/P/C
    pTmgrTls->updateTaintCarryFlag (std::make_shared<TaintBit>(F_CARRY_SUB, objSrcDest, objSrc));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AUXILIARY_SUB, objSrcDest, objSrc));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_ARE_EQUAL, objSrcDest, objSrc));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objResult));
    pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_SUB, objSrcDest, objSrc, objResult));
} // fTaintSUB

/////////
// CMP //
/////////

// CALLBACKS
void BINARY::cCMP(INS &ins) 
{ 	
    void (*callback)() = nullptr;	
    if (INS_OperandIsReg(ins, 0)) // 1ere operande = REGISTRE (IR/MR/RR)
    {
        REG regDest  = INS_OperandReg(ins, 0);
        UINT32 regDestSize = getRegSize(regDest);
        
        if (!regDestSize) return;	// registre non instrumenté
        else if (INS_OperandIsImmediate(ins, 1))  // CMPIR
        {   
            switch (regDestSize) 
            {	
                case 1:	callback = (AFUNPTR) sCMP_IR<8>; break;
                case 2:	callback = (AFUNPTR) sCMP_IR<16>; break;
                case 4:	callback = (AFUNPTR) sCMP_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sCMP_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_IsMemoryRead(ins)) // CMPMR
        {			
            switch (regDestSize) 
            {	
                case 1:	callback = (AFUNPTR) sCMP_MR<8>;  break;
                case 2:	callback = (AFUNPTR) sCMP_MR<16>; break;
                case 4:	callback = (AFUNPTR) sCMP_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sCMP_MR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		// adresse réelle de lecture
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else // CMPRR
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            switch (regDestSize) 
            {	
                case 1:	callback = (AFUNPTR) sCMP_RR<8>;  break;
                case 2:	callback = (AFUNPTR) sCMP_RR<16>; break;
                case 4:	callback = (AFUNPTR) sCMP_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sCMP_RR<64>; break;
                #endif
                default: return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc,		// registre source
                IARG_REG_VALUE, regSrc,		// valeur lors du callback
                IARG_UINT32, regDest,		// registre de destination
                IARG_REG_VALUE, regDest,	// valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }  
    }
    else // 1ere opérande = MEMOIRE (IM/RM)
    {	
        UINT32 memSize = INS_MemoryReadSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // CMPIM
        {	
            switch (memSize) // taille de l'opérande mémoire
            {	
                case 1:	callback = (AFUNPTR) sCMP_IM<8>;  break;
                case 2:	callback = (AFUNPTR) sCMP_IM<16>; break;
                case 4:	callback = (AFUNPTR) sCMP_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sCMP_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYREAD_EA, // et non pas WRITE car CMP ne change pas la dest
                IARG_INST_PTR, IARG_END);
        } 
        else // CMPRM
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sCMP_RM<8>;  break;
                case 2:	callback = (AFUNPTR) sCMP_RM<16>; break;
                case 4:	callback = (AFUNPTR) sCMP_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sCMP_RM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc, 
                IARG_MEMORYREAD_EA, // et non pas WRITE car CMP ne change pas la dest
                IARG_INST_PTR, IARG_END);
        }
    }
} // cCMP

// FLAGS : cf fichier hpp

/////////
// MUL //
/////////

// CALLBACKS
void BINARY::cMUL(INS &ins) 
{ 
    
    void (*callback)() = nullptr;       // pointeur sur la fonction à appeler
    REG implicitReg    = REG_INVALID(); // registre implicite : AL, AX, EAX ou RAX
        
    if (INS_IsMemoryRead(ins)) 
    { 
        // source = mémoire, donc type MUL M
        switch (INS_MemoryReadSize(ins)) 
        {
        case 1:	 callback = (AFUNPTR) sMUL_1M<8>;	implicitReg = REG_AL;  break;
        case 2:	 callback = (AFUNPTR) sMUL_1M<16>;	implicitReg = REG_AX;  break;
        case 4:	 callback = (AFUNPTR) sMUL_1M<32>;	implicitReg = REG_EAX; break;
        #if TARGET_IA32E
        case 8:	 callback = (AFUNPTR) sMUL_1M<64>;  implicitReg = REG_RAX; break;
        #endif
        default: return;
        }
            
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,		     // adresse réelle de lecture 
            IARG_REG_VALUE, implicitReg, // valeur du registre implicite
            IARG_INST_PTR, IARG_END);
    }
    else // source = registre, donc type IMUL 1R.
    {			
        REG regSrc = INS_OperandReg(ins, 0);// registre src en opérande 0
           
        switch (getRegSize(regSrc)) 
        {
        case 1:	 callback = (AFUNPTR) sMUL_1R<8>;	implicitReg = REG_AL;  break;
        case 2:	 callback = (AFUNPTR) sMUL_1R<16>;	implicitReg = REG_AX;  break;
        case 4:	 callback = (AFUNPTR) sMUL_1R<32>;	implicitReg = REG_EAX; break;
        #if TARGET_IA32E
        case 8:	 callback = (AFUNPTR) sMUL_1R<64>;  implicitReg = REG_RAX; break;
        #endif
        default: return;
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,    regSrc, // registre source 1
            IARG_REG_VALUE, regSrc, // sa valeur lors du callback
            IARG_REG_VALUE, implicitReg,// valeur du registre implicite
            IARG_INST_PTR, IARG_END);
    }
} // cMUL

// FLAGS
void BINARY::fTaintMUL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr) 
{
    // MUL = O / P, identiques
    TaintBitPtr flagPtr = std::make_shared<TaintBit>(F_CARRY_MUL, ObjectSource(resultPtr));

    pTmgrTls->updateTaintOverflowFlag(flagPtr);
    pTmgrTls->updateTaintCarryFlag(flagPtr);
} // fTaintMUL

//////////
// IMUL //
//////////

// CALLBACKS
void BINARY::cIMUL(INS &ins) 
{ 
    // CAS 1 (1 OPERANDE INTEL) : SOUS PIN 4 OPERANDES SONT DONNEES 
    // op1(explicite) : source1 (lecture, soit reg soit mem) (LECTURE SEULE)
    // op2(implicite) : source2 (AL/AX/EAX selon taille de la source1) 
    //                  mais aussi destination si 16bits(AX) et 32 bits (EAX)
    // op3(implicite) : destination (AH 8 bits, DX 16 bits, EDX 32bits)
    // op4(implicite) : Eflags

    // CAS 2 (2 OPERANDES INTEL) : SOUS PIN 3 OPERANDES SONT DONNEES 
    // op1(explicite) : source1 et destination (registre 16 ou 32 bits)
    //                  (OPERANDE LECTURE/ECRITURE)
    // op2(explicite) : source2 (16 ou 32bits, Reg/mem/imm)
    //                  même si Imm est plutot codé en cas 3
    // op3(implicite) : Eflags 

    // CAS 3 (3 OPERANDES INTEL) : SOUS PIN 4 OPERANDES SONT DONNEES 
    // op1(explicite) : destination (registre 16 ou 32 bits) (ECRITURE SEULE)
    // op2(explicite) : source1 (16 ou 32bits, Reg/mem)
    // op3(explicite) : source2 (immédiate, 8, 16 ou 32bits) 
    // op4(implicite) : Eflags 

    // pointeur sur la fonction à appeler
    void (*callback)() = nullptr;			

    if (INS_OperandReadAndWritten(ins, 0)) 
    {	
        // Opérande 0 en lecture/ecriture => cas 2 (2 opérandes x86)
        REG regSrcDest = INS_OperandReg(ins, 0); // registre src et dest
        UINT32 regSize = getRegSize(regSrcDest); // taille destination
        
        if (INS_IsMemoryRead(ins)) 
        {			
            // 2eme source = mémoire, donc type reg = mem*reg
            switch (regSize) 
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) sIMUL_2MR<16>;	break;
            case 4:	callback = (AFUNPTR) sIMUL_2MR<32>;	break;
            #if TARGET_IA32E
            case 8:	callback = (AFUNPTR) sIMUL_2MR<64>;	break;
            #endif
            default: return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,			// adresse réelle de lecture
                IARG_UINT32,    regSrcDest, // registre source et destination
                IARG_REG_VALUE, regSrcDest, // sa valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1)) 
        {	
            // 2eme source = immédiate, donc type IMUL2 IR
            // NB: sera codé en cas IMUL3IR, avec regSrc = regSrcDest
            switch (regSize) 
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) sIMUL_3R<16>;	break;
            case 4:	callback = (AFUNPTR) sIMUL_3R<32>;	break;
            #if TARGET_IA32E
            case 8:	callback = (AFUNPTR) sIMUL_3R<64>;	break;
            #endif
            default: return;
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,	// type IMUL IRR
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 2), 
                IARG_UINT32,    regSrcDest,	// source = destination
                IARG_REG_VALUE, regSrcDest,	// sa valeur lors du callback
                IARG_UINT32,    regSrcDest,	// registre destination
                IARG_INST_PTR, IARG_END);
        }
        else // 2ème source = registre
        {	
            switch (regSize) 
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) sIMUL_2RR<16>;	break;
            case 4:	callback = (AFUNPTR) sIMUL_2RR<32>;	break;
            #if TARGET_IA32E
            case 8:	callback = (AFUNPTR) sIMUL_2RR<64>;	break;
            #endif
            default: return;
            }
            REG regSrc = INS_OperandReg(ins, 1);
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback, // type IMUL RR
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc,		// registre source1
                IARG_REG_VALUE, regSrc,		// sa valeur lors du callback
                IARG_UINT32,    regSrcDest, // registre dest et source2
                IARG_REG_VALUE, regSrcDest, // sa valeur lors du callback
                IARG_INST_PTR, IARG_END);
        }
    }
    // 1ere opérande en écriture seule => cas 3
    else if (INS_OperandWrittenOnly(ins, 0)) 
    {		
        REG regDest		= INS_OperandReg(ins, 0);	// registre destination
        UINT32 regSize	= getRegSize(regDest);		// taille destination 
    
        if (INS_IsMemoryRead(ins))  // 2eme source = mémoire, type IMUL3 IM
        {
            switch (regSize) 
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) sIMUL_3M<16>;	break;
            case 4:	callback = (AFUNPTR) sIMUL_3M<32>;	break;
            #if TARGET_IA32E
            case 8:	callback = (AFUNPTR) sIMUL_3M<64>;	break;
            #endif
            default:	return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 2), 
                IARG_MEMORYREAD_EA,		// adresse réelle de lecture (source1)
                IARG_UINT32, regDest,	// registre destination
                IARG_INST_PTR, IARG_END);
        }
        else // 2eme source = registre, donc type IMUL3 IR
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            
            switch (getRegSize(regSrc)) 
            {
            // case 1:	impossible
            case 2:	callback = (AFUNPTR) sIMUL_3R<16>;	break;
            case 4:	callback = (AFUNPTR) sIMUL_3R<32>;	break;
            #if TARGET_IA32E
            case 8:	callback = (AFUNPTR) sIMUL_3R<64>;	break;
            #endif
            default: return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,	// type IMUL IRR
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 2), 
                IARG_UINT32,    regSrc,		// registre source1
                IARG_REG_VALUE, regSrc,		// sa valeur lors du callback
                IARG_UINT32,    regDest,	// registre destination
                IARG_INST_PTR,	IARG_END);
        }
    }										  
    else // sinon on se trouve dans le cas 1 (une seule opérande explicite)
    {	 
        REG implicitReg; // registre implicite : AL, AX, EAX ou RAX
        if (INS_IsMemoryRead(ins)) 
        { 
            // source = mémoire, donc type IMUL M
            switch (INS_MemoryReadSize(ins)) 
            {
            case 1:	
                callback = (AFUNPTR) sIMUL_1M<8>;	
                implicitReg = REG_AL;
                break;
            case 2:	
                callback = (AFUNPTR) sIMUL_1M<16>;	
                implicitReg = REG_AX;
                break;
            case 4:	
                callback = (AFUNPTR) sIMUL_1M<32>;	
                implicitReg = REG_EAX;
                break;
            #if TARGET_IA32E
            case 8:	
                callback = (AFUNPTR) sIMUL_1M<64>;	
                implicitReg = REG_RAX;
                break;
            #endif
            default: return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		     // adresse réelle de lecture 
                IARG_REG_VALUE, implicitReg, // valeur du registre implicite
                IARG_INST_PTR, IARG_END);
        }
        else // source = registre, donc type IMUL 1R.
        {			
            REG regSrc = INS_OperandReg(ins, 0);// registre src
           
            switch (getRegSize(regSrc)) 
            {
            case 1:	
                callback = (AFUNPTR) sIMUL_1R<8>;	
                implicitReg = REG_AL;
                break;
            case 2:	
                callback = (AFUNPTR) sIMUL_1R<16>;	
                implicitReg = REG_AX;
                break;
            case 4:	
                callback = (AFUNPTR) sIMUL_1R<32>;	
                implicitReg = REG_EAX;
                break;
            #if TARGET_IA32E
            case 8:	
                callback = (AFUNPTR) sIMUL_1R<64>;	
                implicitReg = REG_RAX;
                break;
            #endif
            default: return;
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc, // registre source 1
                IARG_REG_VALUE, regSrc, // sa valeur lors du callback
                IARG_REG_VALUE, implicitReg,// valeur du registre implicite
                IARG_INST_PTR, IARG_END);
        }
    }
}

// FLAGS
void BINARY::fTaintIMUL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr)
{
    // IMUL = OF / CF, marquage identique, autres flags inchangés
    TaintBitPtr flagPtr = std::make_shared<TaintBit>(F_CARRY_IMUL, ObjectSource(resultPtr));

    pTmgrTls->updateTaintOverflowFlag(flagPtr);
    pTmgrTls->updateTaintCarryFlag(flagPtr);
}

////////////////////////////
// DIVISION (DIV et IDIV) //
////////////////////////////

// CALLBACKS
void BINARY::cDIVISION(INS &ins, bool isSignedDivision)
{
    // division : le dividende sera réparti sur deux variables marquées
    // exemple sur 16 bits : 
    // - DX:AX est divisé par r/m16, quotient dans AX, reste dans DX
    // - AX sera marqué avec IDIV_QUO/DIV_QUO 
    // - DX sera marqué avec IDIV_REM/DIV_REM 
    // les procédures DIV/IDIV sont strictement les mêmes, seule la relation change
    // etant donné qu'il y a peu de chances de rencontrer ce type d'instruction
    // on se permet de passer le type signed/unsigned par parametre (pas par template)
    void (*callback)()  = nullptr;
    REG lowDividendReg  = REG_INVALID(); // AL/AX/EAX/RAX 
    REG highDividendReg = REG_INVALID();// AH/DX/EDX/RDX 

    if (INS_IsMemoryRead(ins)) 
    {	
        // source = mémoire, donc type IDIV M. 
        // Dividende = AX, DX:AX, EDX:EAX ou RDX::RAX selon la taille de la mémoire

        switch (INS_MemoryReadSize(ins)) 
        {
        case 1:	
            callback = (AFUNPTR) sDIVISION_M<8>; 
            lowDividendReg = REG_AL;
            highDividendReg = REG_AH;
            break;
        case 2:	
            callback = (AFUNPTR) sDIVISION_M<16>; 
            lowDividendReg = REG_AX;
            highDividendReg = REG_DX;
            break;
        case 4:	
            callback = (AFUNPTR) sDIVISION_M<32>; 
            lowDividendReg = REG_EAX;
            highDividendReg = REG_EDX;
            break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sDIVISION_M<64>;
            lowDividendReg = REG_RAX;
            highDividendReg = REG_RDX;
            break;
        #endif
        default: return;
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,			// adresse réelle de lecture 
            IARG_BOOL, isSignedDivision,    // true = division signée
            IARG_REG_VALUE, lowDividendReg,	// valeur de AL/AX/EAX/RAX lors du callback  
            IARG_REG_VALUE, highDividendReg,	// valeur de AH/DX/EDX/RDX lors du callback
            IARG_INST_PTR, IARG_END);
    }
    else
    {
        REG regSrc = INS_OperandReg(ins, 0);	// registre src
        switch (getRegSize(regSrc))
        {
        case 1:	
            callback = (AFUNPTR) sDIVISION_R<8>; 
            lowDividendReg = REG_AL;
            highDividendReg = REG_AH;
            break;
        case 2:	
            callback = (AFUNPTR) sDIVISION_R<16>; 
            lowDividendReg = REG_AX;
            highDividendReg = REG_DX;
            break;
        case 4:	
            callback = (AFUNPTR) sDIVISION_R<32>; 
            lowDividendReg = REG_EAX;
            highDividendReg = REG_EDX;
            break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sDIVISION_R<64>;
            lowDividendReg = REG_RAX;
            highDividendReg = REG_RDX;
            break;
        #endif
        default: return;
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,    regSrc, // registre source 1
            IARG_REG_VALUE, regSrc, // sa valeur lors du callback
            IARG_BOOL, isSignedDivision,    // true = division signée
            IARG_REG_VALUE, lowDividendReg,	// valeur de AL/AX/EAX/RAX lors du callback  
            IARG_REG_VALUE, highDividendReg,// valeur de AH/DX/EDX/RDX lors du callback
            IARG_INST_PTR, IARG_END);
    }
}// cDIVISION
