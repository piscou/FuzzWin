#include "dataxfer.h"
#include <TaintUtilities\utils.h>

/////////
// MOV //
/////////

// CALLBACKS
void DATAXFER::cMOV(INS &ins) 
{
    void (*callback)() = nullptr;	// pointeur sur la fonction à appeler

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {	
        UINT32 writeSize = INS_MemoryWriteSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // valeur immédiate -> démarquage
        { 
            INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) UTILS::uMEM,
                IARG_FAST_ANALYSIS_CALL,  
                IARG_MEMORYWRITE_EA,  
                IARG_UINT32, writeSize,
                IARG_END);
        } 
        else // registre -> Mémoire
        { 
            switch (writeSize) 
            {
            case 1:	callback = (AFUNPTR) sMOV_RM<8>;  break;
            case 2:	callback = (AFUNPTR) sMOV_RM<16>; break;
            case 4:	callback = (AFUNPTR) sMOV_RM<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sMOV_RM<64>; break;
            #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, INS_OperandReg(ins, 1),   
                IARG_MEMORYWRITE_EA,
                IARG_INST_PTR, IARG_END);
        }
    }
    else     // DESTINATION = REGISTRE
    {	
        REG regDest  = INS_OperandReg(ins, 0);
        UINT32 regSize = getRegSize(regDest);

        if (!regSize) return;   // registre destination non suivi
        else if (INS_IsMemoryRead(ins)) // Mémoire -> Registre
        {                     

            switch (regSize)
            {
            case 1:	callback = (AFUNPTR) sMOV_MR<8>;  break;
            case 2:	callback = (AFUNPTR) sMOV_MR<16>; break;
            case 4:	callback = (AFUNPTR) sMOV_MR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sMOV_MR<64>; break;
            #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		
                IARG_UINT32, regDest,   
                IARG_INST_PTR, IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1)) // Valeur : démarquage
        {	
            switch (regSize)
            {
            case 1:	callback = (AFUNPTR) UTILS::uREG<8>;	break;
            case 2:	callback = (AFUNPTR) UTILS::uREG<16>;	break;
            case 4:	callback = (AFUNPTR) UTILS::uREG<32>;	break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) UTILS::uREG<64>;	break;
            #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_FAST_ANALYSIS_CALL, 
                IARG_THREAD_ID,
                IARG_UINT32, regDest, IARG_END);
        }
        else // registre -> registre
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc))  
            {
            case 0 : return; // cas registre source non suivi
            case 1:	callback = (AFUNPTR) sMOV_RR<8>;  break;
            case 2:	callback = (AFUNPTR) sMOV_RR<16>; break;
            case 4:	callback = (AFUNPTR) sMOV_RR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sMOV_RR<64>; break;
            #endif
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc,		
                IARG_UINT32, regDest, 
                IARG_INST_PTR, IARG_END);
        }  
    }
} // cMOV

// SIMULATE (templates spécialisés)
template<> void DATAXFER::sMOV_RR<8>(THREADID tid, REG regSrc, REG regDest, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<8>(regSrc))   pTmgrTls->unTaintRegister<8>(regDest);
    else 
    {
        _LOGTAINT(tid, insAddress, "movRR8");
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_ASSIGN, 
            ObjectSource(pTmgrTls->getRegisterTaint(regSrc))));
    }
} // sMOV_RR<8>

template<> void DATAXFER::sMOV_RM<8>(THREADID tid, REG regSrc, ADDRINT writeAddress, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if (!pTmgrTls->isRegisterTainted<8>(regSrc)) pTmgrGlobal->unTaintMemory<8>(writeAddress);
    else 
    {
        _LOGTAINT(tid, insAddress, "movRM8 de" + REG_StringShort(regSrc) + " vers addresse " + hexstr(writeAddress));
        pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
            X_ASSIGN, 
            ObjectSource(pTmgrTls->getRegisterTaint(regSrc))));
    }
} // sMOV_RM<8>

template<> void DATAXFER::sMOV_MR<8>(THREADID tid, ADDRINT readAddress, REG regDest, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if (!pTmgrGlobal->isMemoryTainted<8>(readAddress)) pTmgrTls->unTaintRegister<8>(regDest);
    else 
    {
        _LOGTAINT(tid, insAddress, "movMR8 de l'addresse " + hexstr(readAddress) + " vers " + REG_StringShort(regDest));
        pTmgrTls->updateTaintRegister<8>(regDest, std::make_shared<TaintByte>(
            X_ASSIGN, 
            ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
    }
} // sMOV_MR<8>

//////////
// XCHG //
//////////

// CALLBACKS
void DATAXFER::cXCHG(INS &ins) 
{
    void (*callback)() = nullptr;	

    if (INS_IsMemoryWrite(ins)) // src = reg, dest = mémoire
    { 
        switch (INS_MemoryWriteSize(ins)) 
        {	
        case 1:	callback = (AFUNPTR) sXCHG_M<8>;  break;
        case 2:	callback = (AFUNPTR) sXCHG_M<16>; break;
        case 4:	callback = (AFUNPTR) sXCHG_M<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sXCHG_M<64>; break;
        #endif
        }
        // le registre peut être soit en opérande 0, soit en 1
        // donc utilisation de regW
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, INS_RegW(ins, 0),	// registre source
            IARG_MEMORYWRITE_EA,    // adresse réelle d'écriture 
            IARG_INST_PTR, IARG_END);
    }
    else // échange registre / registre
    {                      
        REG regDest = INS_OperandReg(ins, 0);
        REG regSrc  = INS_OperandReg(ins, 1);

        if (regSrc == regDest) return;	// ca arrive parfois...

        switch (getRegSize(regDest)) 
        {
        case 1:	callback = (AFUNPTR) sXCHG_R<8>;  break;
        case 2:	callback = (AFUNPTR) sXCHG_R<16>; break;
        case 4:	callback = (AFUNPTR) sXCHG_R<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sXCHG_R<64>; break;
        #endif
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, regSrc,	
            IARG_UINT32, regDest,	   
            IARG_INST_PTR, IARG_END);
    }
} // cXCHG

// SIMULATE (templates spécialisés)
template<> void DATAXFER::sXCHG_M<8>(THREADID tid, REG reg, ADDRINT address, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    TaintBytePtr tbTempPtr; // variable de mise en cache
    REGINDEX regIndex = getRegIndex(reg);
    
    // récupération du marquage de la mémoire (nullptr si absent)
    tbTempPtr = pTmgrGlobal->getMemoryTaint<8>(address);

    // récupération du marquage du registre et affectation directe à la mémoire
    if (pTmgrTls->isRegisterTainted<8>(reg))
    {
        pTmgrGlobal->updateMemoryTaint<8>(address, pTmgrTls->getRegisterTaint(reg));
    }
    else pTmgrGlobal->unTaintMemory<8>(address);

    // affectation de la variable temporaire au registre
    if (tbTempPtr) pTmgrTls->updateTaintRegister<8>(reg, tbTempPtr);
    else pTmgrTls->unTaintRegister<8>(reg);
} // sXCHG_M<8>

template<> void DATAXFER::sXCHG_R<8>(THREADID tid, REG regSrc, REG regDest, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    TaintBytePtr tbTempPtr; // variable de mise en cache
            
    // récupération du marquage du registre destination (nullptr si absent)
    tbTempPtr = pTmgrTls->getRegisterTaint(regDest); 

    // récupération du marquage du registre src et affectation directe à la destination
    if (pTmgrTls->isRegisterTainted<8>(regSrc))
    {
        pTmgrTls->updateTaintRegister<8>(regDest, pTmgrTls->getRegisterTaint(regSrc));
    }
    else pTmgrTls->unTaintRegister<8>(regDest);

    // affectation de la variable temporaire au registre
    if (tbTempPtr) pTmgrTls->updateTaintRegister<8>(regSrc, tbTempPtr);
    else pTmgrTls->unTaintRegister<8>(regSrc);
} // sXCHG_R<8>

///////////
// BSWAP //
///////////

// CALLBACKS
void DATAXFER::cBSWAP(INS &ins)
{
    REG reg = INS_OperandReg(ins, 0);	// registre à inverser 
    
    #if TARGET_IA32 // mode 32bits : une seule instruction possible
    INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sBSWAP<32>,		 
        IARG_THREAD_ID,
        IARG_UINT32, reg, 
        IARG_INST_PTR, IARG_END);
    #else
    void (*callback)() = nullptr;
    callback = (getRegSize(reg) == 4) ? (AFUNPTR) sBSWAP<32> : (AFUNPTR) sBSWAP<64>;
    INS_InsertCall (ins, IPOINT_BEFORE, callback,		 
        IARG_THREAD_ID,
        IARG_UINT32, reg, 
        IARG_INST_PTR, IARG_END);
    #endif
} // cBSWAP

///////////
// MOVSX //
///////////

// CALLBACKS
void DATAXFER::cMOVSX(INS &ins) 
{
    void (*callback)() = nullptr;

    // identifiant du registre de destination
    REG regDest			= INS_OperandReg(ins, 0);	
    // taille du registre de destination
    UINT32 regDestSize	= getRegSize(regDest);		
    
    if (!regDestSize) return;   // registre de destination non supporté
    
    else if (INS_IsMemoryRead(ins)) // Source = mémoire 
    {			
        UINT32 readSize = INS_MemoryReadSize(ins);
        switch (regDestSize) 
        {
        case 2:	callback = (AFUNPTR) sMOVSX_MR<8, 16>;	break;
        case 4:	callback = (readSize == 1) 
                ? (AFUNPTR) sMOVSX_MR<8, 32> 
                : (AFUNPTR) sMOVSX_MR<16, 32>;
            break;
        #if TARGET_IA32E
        case 8: 
            switch (readSize)
            {
            case 1: callback = (AFUNPTR) sMOVSX_MR<8, 64>;	break;
            case 2: callback = (AFUNPTR) sMOVSX_MR<16, 64>;	break;
            // case 4: sMOVSX_MR<32, 64> => traité en MOVSXD	break;
            }
        #endif
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,  
            IARG_UINT32, regDest,
            IARG_INST_PTR, IARG_END);
    }
    else // Source = registre
    {	
        // identifiant du registre source
        REG regSrc = INS_OperandReg(ins, 1);
        // taille du registre source
        UINT32 readSize = getRegSize(regSrc);

        switch (readSize) 
        {
        case 0 : return;    // registre source non supporté
        case 1: // source sur 8bits
            switch (regDestSize)
            {
            case 2:	callback = (AFUNPTR) sMOVSX_RR<8, 16>; break;
            case 4: callback = (AFUNPTR) sMOVSX_RR<8, 32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sMOVSX_RR<8, 64>; break;
            #endif
            }
            break;
        case 2: // source sur 16bits
            #if TARGET_IA32E
            callback = (regDestSize == 4) // destinations possibles en x64 : 32 ou 64bits
                ? (AFUNPTR) sMOVSX_RR<16, 32>
                : (AFUNPTR) sMOVSX_RR<16, 64>;
            #else
            callback = (AFUNPTR) sMOVSX_RR<16, 32>; // x86 : seulement dest 32bits
            #endif
            break;
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,	 regSrc,
            IARG_REG_VALUE,  regSrc,
            IARG_UINT32,	regDest,
            IARG_INST_PTR, IARG_END);       
    }
} // cMOVSX

#if TARGET_IA32E
void DATAXFER::cMOVSXD(INS &ins) 
{
    // en x64 uniquement : idem MOVSX, EA sur 32bits, regDest sur 64bits

    // identifiant du registre de destination
    REG regDest	= INS_OperandReg(ins, 0);	

    // taille du registre de destination nul <=> registre non suivi
    if (! getRegSize(regDest)) return; 
    else if (INS_IsMemoryRead(ins)) // Source = mémoire 
    {			
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sMOVSX_MR<32, 64>,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,  
            IARG_UINT32, regDest,
            IARG_INST_PTR, IARG_END);
    }
    else // Source = registre
    {	
        // identifiant du registre source
        REG regSrc = INS_OperandReg(ins, 1);
        // taille du registre source nul <=> registre non suivi
        if (! getRegSize(regSrc)) return; 

        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) sMOVSX_RR<32, 64>,
            IARG_THREAD_ID,
            IARG_UINT32,	 regSrc,
            IARG_REG_VALUE,  regSrc,
            IARG_UINT32,	regDest,
            IARG_INST_PTR, IARG_END);
    }
} // cMOVSXD
#endif

///////////
// MOVZX //
///////////

// CALLBACKS
void DATAXFER::cMOVZX(INS &ins) 
{
    // identifiant du registre de destination
    REG regDest			= INS_OperandReg(ins, 0);
    // taille du registre de destination	
    UINT32 regDestSize	= getRegSize(regDest);		
    void (*callback)() = nullptr;
    
    if (!regDestSize) return; 
    else if (INS_IsMemoryRead(ins)) // Source = mémoire
    {			 
        UINT32 readSize = INS_MemoryReadSize(ins);
        switch (regDestSize) 
        {
        case 2:	callback = (AFUNPTR) sMOVZX_MR<8, 16>; break;
        case 4: callback = (readSize == 1) 
                    ? (AFUNPTR) sMOVZX_MR<8, 32> 
                    : (AFUNPTR) sMOVZX_MR<16, 32>;
            break;
        #if TARGET_IA32E
        case 8: 
            switch (readSize)
            {
            case 1: callback = (AFUNPTR) sMOVZX_MR<8, 64>;	break;
            case 2: callback = (AFUNPTR) sMOVZX_MR<16, 64>;	break;
            case 4: callback = (AFUNPTR) sMOVZX_MR<32, 64>;	break;
            }
        #endif
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,  
            IARG_UINT32, regDest,
            IARG_INST_PTR, IARG_END);
    }
    else // Source = registre
    {	
        // identifiant du registre source
        REG regSrc = INS_OperandReg(ins, 1);
        // taille du registre source
        UINT32 readSize = getRegSize(regSrc);

        // si le registre source est sur 8bits, appel du template spécifique sMOVZX_8R
        if (!readSize) return;  // registre source non supporté
        else if (readSize == 1)
        {
            switch (regDestSize) 
            {
            case 2:	callback = (AFUNPTR) sMOVZX_8R<16>;	break;
            case 4: callback = (AFUNPTR) sMOVZX_8R<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sMOVZX_8R<64>; break;
            #endif
            }
        }
        else 
        // registre source de 16 (voire 32bits en x64)
        // destination 32bits (voire 64bits en x64)
        {	   
            #if TARGET_IA32E
            switch (regDestSize) 
            {
            case 4:	callback = (AFUNPTR) sMOVZX_RR<16, 32>; break;
            case 8: 
                callback = (readSize == 2) 
                    ? (AFUNPTR) sMOVZX_RR<16, 64> 
                    : (AFUNPTR) sMOVZX_RR<32, 64>;
                break;
            }
            #else
            callback = (AFUNPTR) sMOVZX_RR<16, 32>;
            #endif 	
        }
        
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, regSrc, 
            IARG_UINT32, regDest,
            IARG_INST_PTR, IARG_END);
    }
 } // cMOVZX
