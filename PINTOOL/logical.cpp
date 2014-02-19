#include "LOGICAL.h"
#include "utils.h"

// fonction de marquage des flags commune à toutes les instructions LOGICAL
void LOGICAL::fTaintLOGICAL(TaintManager_Thread *pTmgrTls, const TaintPtr &resultPtr) 
{
    // LOGICAL : O et C mis à 0, marquage S/Z/P
    // et démarquage AF ("undefined" selon Intel)
    pTmgrTls->unTaintCarryFlag();
    pTmgrTls->unTaintOverflowFlag();
    pTmgrTls->unTaintAuxiliaryFlag();

    ObjectSource objResult(resultPtr);
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objResult));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>  (F_IS_NULL, objResult));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>  (F_MSB,     objResult));
} // fTaintLOGICAL

///////////////
///// AND /////
///////////////

// CALLBACKS
void LOGICAL::cAND(INS &ins) 
{
    // pointeur sur la fonction à appeler (marquage destination)
    void (*callback)() = nullptr;

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {
        if (INS_OperandIsImmediate(ins, 1)) // AND_IM
        {
            switch (INS_MemoryWriteSize(ins)) // taille de l'opérande mémoire
            {
                case 1: callback = (AFUNPTR) sAND_IM<8>;  break;
                case 2: callback = (AFUNPTR) sAND_IM<16>; break;
                case 4: callback = (AFUNPTR) sAND_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sAND_IM<64>; break;
                #endif
                default: return; // autres cas non gérés
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                CALLBACK_DEBUG IARG_END);
        } 
        else  // AND_RM
        {
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {
                case 1: callback = (AFUNPTR) sAND_RM<8>;  break;
                case 2: callback = (AFUNPTR) sAND_RM<16>; break;
                case 4: callback = (AFUNPTR) sAND_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sAND_RM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,
                CALLBACK_DEBUG IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest = INS_OperandReg(ins, 0);
        UINT32 regDestSize = getRegSize(regDest);
        
        if (!regDestSize) return;       // registre destination non suivi
        else if (INS_IsMemoryRead(ins)) // AND_MR
        {
            switch (regDestSize) // taille de l'opérande mémoire
            {
                case 1: callback = (AFUNPTR) sAND_MR<8>;  break;
                case 2: callback = (AFUNPTR) sAND_MR<16>; break;
                case 4: callback = (AFUNPTR) sAND_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sAND_MR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA, 
                IARG_UINT32, regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1)) // AND_IR
        {    
            switch (regDestSize) 
            {
                case 1: callback = (AFUNPTR) sAND_IR<8>; break;
                case 2: callback = (AFUNPTR) sAND_IR<16>; break;
                case 4: callback = (AFUNPTR) sAND_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sAND_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }
        else // AND_RR
        {    
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {
                case 1: callback = (AFUNPTR) sAND_RR<8>;  break;
                case 2: callback = (AFUNPTR) sAND_RR<16>; break;
                case 4: callback = (AFUNPTR) sAND_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sAND_RR<64>; break;
                #endif
                default: return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc,  
                IARG_REG_VALUE, regSrc,
                IARG_UINT32,    regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }  
    }
} // cAND

// SIMULATE (spécialisation des templates)
template<> void LOGICAL::sAND_IM<8>(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if (!pTmgrGlobal->isMemoryTainted<8>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else if (!value) // AND x, 0 = 0, donc démarquage destination et flags
    { 
        pTmgrTls->unTaintAllFlags();
        pTmgrGlobal->unTaintMemory<8>(writeAddress);
    }
    else 
    {
        _LOGTAINT("andIM(8)");
        // AND x, 0xff = x, donc juste marquage flags avec destination
        if (value == 0xff)  fTaintLOGICAL(pTmgrTls, pTmgrGlobal->getMemoryTaint<8>(writeAddress));
        else // sinon marquage "normal" : flags + destination
        { 
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_AND,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                ObjectSource(8, value));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr);        
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
        }
    }
} // sAND_IM<8>

template<> void LOGICAL::sAND_IR<8>(THREADID tid, ADDRINT value, REG reg, ADDRINT unUsed ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<8>(reg)) pTmgrTls->unTaintAllFlags();
    else if (!value)  // AND x, 0 = 0, donc démarquage destination et flags
    {
        pTmgrTls->unTaintAllFlags();
        pTmgrTls->unTaintRegister<8>(reg);
    }
    else 
    {
        _LOGTAINT("andIR(8)");      
        // AND x, 0xff = x, donc juste marquage flags avec destination
        if (value == 0xff) fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(reg));
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_AND,
                ObjectSource(pTmgrTls->getRegisterTaint(reg)),
                ObjectSource(8, value));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr);
            pTmgrTls->updateTaintRegister<8>(reg, resultPtr);
        }
    }
} // AND_IR_8

template<> void LOGICAL::sAND_RM<8>
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrGlobal->isMemoryTainted<8>(writeAddress);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<8>(regSrc);

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("andRM(8)");
        // récupération de la valeur de la mémoire
        ADDRINT destValue = getMemoryValue<8>(writeAddress);

        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0 => démarquage flags (dest deja non marquée)
            if (!destValue)  pTmgrTls->unTaintAllFlags();
            // cas 2.2 : destination vaut 0xff ; (AND 0xff, src) équivaut à MOV dest, src
            else if (destValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
            }
            // cas 2.3 : autres valeur de la destination => marquage via AND
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0 ; (AND dest, 0) = 0, donc démarquer destination et flags
            if (!srcValue) 
            {
                pTmgrTls->unTaintAllFlags();
                pTmgrGlobal->unTaintMemory<8>(writeAddress);
            }
            // cas 3.2 : src vaut 0xff => AND dest, 0xff ne modifie pas dest => marquage flags avec valeur actuelle destination
            else if (srcValue == 0xff)  
            {
                fTaintLOGICAL(pTmgrTls, pTmgrGlobal->getMemoryTaint<8>(writeAddress));
            }
            // cas 3.3 : autres valeur de la source => marquage via AND
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                    ObjectSource(8, srcValue)); 
            
                fTaintLOGICAL(pTmgrTls, resultPtr); 
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via AND
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_AND,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                ObjectSource(pTmgrTls->getRegisterTaint(regSrc))); 
            
            fTaintLOGICAL(pTmgrTls, resultPtr); 
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
        }   
    }
} // sAND_RM<8>

template<> void LOGICAL::sAND_MR<8>
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrTls->isRegisterTainted<8>(regSrcDest);
    bool isSrcTainted  = pTmgrGlobal->isMemoryTainted<8>(readAddress);  

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("andMR(8)");
        // récupération de la valeur de la mémoire
        ADDRINT srcValue = getMemoryValue<8>(readAddress);

        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0 => démarquage flags (dest deja non marquée)
            if (!destValue) pTmgrTls->unTaintAllFlags();
            // cas 2.2 : destination vaut 0xff ; (AND 0xff, src) équivaut à MOV dest, src
            else if (destValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via AND
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0 ; (AND dest, 0) = 0, donc démarquer destination et flags
            if (!srcValue) 
            {
                pTmgrTls->unTaintAllFlags();
                pTmgrTls->unTaintRegister<8>(regSrcDest);
            }
            // cas 3.2 : src vaut 0xff => (AND dest, 0xff) ne modifie pas dest => marquage flags avec valeur actuelle destination
            else if (srcValue == 0xff)
            {
                fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(regSrcDest));
            }
            // cas 3.3 : autres valeur de la source => marquage via AND
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                    ObjectSource(8, srcValue)); 
            
                fTaintLOGICAL(pTmgrTls, resultPtr); 
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr); 
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via AND
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_AND,
                ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))); 
            
            fTaintLOGICAL(pTmgrTls, resultPtr);
            pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr); 
        }   
    }
} // sAND_MR<8>

template<> void LOGICAL::sAND_RR<8>
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrTls->isRegisterTainted<8>(regSrcDest);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<8>(regSrc);  

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("andRR(8)");
        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0 => démarquage flags (dest deja non marquée)
            if (!destValue)  pTmgrTls->unTaintAllFlags();
            // cas 2.2 : destination vaut 0xff => AND 0xff, src équivaut à MOV dest, src
            else if (destValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister(regSrcDest, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via AND
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister(regSrcDest, resultPtr); 
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0 => AND dest, 0 fera tjs 0, donc démarquer destination et flags
            if (!srcValue) 
            {
                pTmgrTls->unTaintAllFlags();
                pTmgrTls->unTaintRegister<8>(regSrcDest);
            }
            // cas 3.2 : src vaut 0xff => and dest, 0xff ne modifie pas dest => marquage flags avec valeur actuelle destination
            else if (srcValue == 0xff)  
            {
                fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(regSrcDest));
            }
            // cas 3.3 : autres valeur de la source => marquage via AND
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                    ObjectSource(8, srcValue)); 
                    
                fTaintLOGICAL(pTmgrTls, resultPtr);
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr); 
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via AND
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_AND,
                ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)), 
                ObjectSource(pTmgrTls->getRegisterTaint(regSrc))); 

            fTaintLOGICAL(pTmgrTls, resultPtr);
            pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);  
        }   
    }
} // AND_RR<8>

//////////////
///// OR /////
//////////////

// CALLBACKS
void LOGICAL::cOR(INS &ins) 
{
    // pointeur sur la fonction à appeler (marquage destination)
    void (*callback)() = nullptr;

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {
        if (INS_OperandIsImmediate(ins, 1)) // OR_IM
        {
            switch (INS_MemoryWriteSize(ins)) // taille de l'opérande mémoire
            {
                case 1: callback = (AFUNPTR) sOR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sOR_IM<16>; break;
                case 4: callback = (AFUNPTR) sOR_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sOR_IM<64>; break;
                #endif
                default: return; // autres cas non gérés
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                CALLBACK_DEBUG IARG_END);
        } 
        else  // OR_RM
        {
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {
                case 1: callback = (AFUNPTR) sOR_RM<8>;  break;
                case 2: callback = (AFUNPTR) sOR_RM<16>; break;
                case 4: callback = (AFUNPTR) sOR_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sOR_RM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,
                CALLBACK_DEBUG IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest = INS_OperandReg(ins, 0);
        UINT32 regDestSize = getRegSize(regDest);
        
        if (!regDestSize) return;       // registre destination non suivi
        else if (INS_IsMemoryRead(ins)) // OR_MR
        {
            switch (regDestSize) // taille de l'opérande mémoire
            {
                case 1: callback = (AFUNPTR) sOR_MR<8>;  break;
                case 2: callback = (AFUNPTR) sOR_MR<16>; break;
                case 4: callback = (AFUNPTR) sOR_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sOR_MR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA, 
                IARG_UINT32, regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1)) // OR_IR
        {    
            switch (regDestSize) 
            {
                case 1: callback = (AFUNPTR) sOR_IR<8>; break;
                case 2: callback = (AFUNPTR) sOR_IR<16>; break;
                case 4: callback = (AFUNPTR) sOR_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sOR_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }
        else // OR_RR
        {    
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {
                case 1: callback = (AFUNPTR) sOR_RR<8>;  break;
                case 2: callback = (AFUNPTR) sOR_RR<16>; break;
                case 4: callback = (AFUNPTR) sOR_RR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sOR_RR<64>; break;
                #endif
                default: return;
            }
            
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regSrc,  
                IARG_REG_VALUE, regSrc,
                IARG_UINT32,    regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }  
    }
} // cOR

// SIMULATE (spécialisation des templates)
template<> void LOGICAL::sOR_IM<8>(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if ( !pTmgrGlobal->isMemoryTainted<8>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else if (value == 0xff) 
    { 
        // OR x, 0xff = 0xff, donc démarquage destination et flags
        pTmgrTls->unTaintAllFlags();
        pTmgrGlobal->unTaintMemory<8>(writeAddress);
    }
    else
    {
        _LOGTAINT("orIM(8)");
        // OR x, 0 = x, donc juste marquage flags avec destination  
        if (!value) fTaintLOGICAL(pTmgrTls, pTmgrGlobal->getMemoryTaint<8>(writeAddress));
        else // sinon marquage "normal"
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_OR,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                ObjectSource(8, value));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr);        
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
        }
    }
} // sOR_IM<8>

template<> void LOGICAL::sOR_IR<8>(THREADID tid, ADDRINT value, REG reg, ADDRINT unUsed ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<8>(reg))  pTmgrTls->unTaintAllFlags();
    else if (value == 0xff)  // OR x, 0xff = 0xff, donc démarquage destination et flags
    {
        pTmgrTls->unTaintAllFlags();
        pTmgrTls->unTaintRegister<8>(reg);
    }
    else
    {
        _LOGTAINT("orIR(8)");

        // OR x, 0 = x, donc juste marquage flags avec destination
        if (!value) fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(reg));
        else
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_OR,
                ObjectSource(pTmgrTls->getRegisterTaint(reg)),
                ObjectSource(8, value));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr);
            pTmgrTls->updateTaintRegister<8>(reg, resultPtr);     
        }
    }
} // sOR_IR<8>

template<> void LOGICAL::sOR_RM<8>
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrGlobal->isMemoryTainted<8>(writeAddress);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<8>(regSrc);

    // CAS 1 : destination et sources non marquée => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("orRM(8)");

        // récupération de la valeur de la mémoire
        ADDRINT destValue = getMemoryValue<8>(writeAddress);

        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0xff => démarquage flags (dest deja non marquée)
            if (destValue == 0xff)  pTmgrTls->unTaintAllFlags();
            else if (!destValue) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via OR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);  
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0xff ; (OR dest, 0xff) = 0xff, donc démarquer dest et flags
            if (srcValue == 0xff) 
            {
                pTmgrTls->unTaintAllFlags();
                pTmgrGlobal->unTaintMemory<8>(writeAddress);
            }
            // cas 3.2 : src vaut 0 => OR dest, 0 ne modifie pas dest 
            // => marquage flags avec valeur actuelle destination
            else if (!srcValue)
            {
                fTaintLOGICAL(pTmgrTls, pTmgrGlobal->getMemoryTaint<8>(writeAddress));
            }
            // cas 3.3 : autres valeur de la source => marquage via OR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                    ObjectSource(8, srcValue)); 
            
                fTaintLOGICAL(pTmgrTls, resultPtr); 
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via OR
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_OR,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                ObjectSource(pTmgrTls->getRegisterTaint(regSrc))); 
            
            fTaintLOGICAL(pTmgrTls, resultPtr); 
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr); 
        }       
    }
} // sOR_RM<8>

template<> void LOGICAL::sOR_MR<8>
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrTls->isRegisterTainted<8>(regSrcDest);
    bool isSrcTainted  = pTmgrGlobal->isMemoryTainted<8>(readAddress);  

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("orMR(8)");
        // récupération de la valeur de la mémoire
        ADDRINT srcValue = getMemoryValue<8>(readAddress);

        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0xff => démarquage flags (dest deja non marquée)
            if (destValue == 0xff)  pTmgrTls->unTaintAllFlags();
            // cas 2.2 : destination vaut 0 ; (OR 0, src) équivaut à MOV dest, src
            else if (!destValue) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via OR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);    
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0xff ; (OR dest, 0xff) = 0xff, donc démarquer dest et flags
            if (srcValue == 0xff) 
            {
                pTmgrTls->unTaintAllFlags();
                pTmgrTls->unTaintRegister<8>(regSrcDest);
            }
            // cas 3.2 : src vaut 0 => OR dest, 0 ne modifie pas dest => marquage flags avec valeur actuelle destination
            else if (!srcValue) 
            {
                fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(regSrcDest));
            }
            // cas 3.3 : autres valeur de la source => marquage via OR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                    ObjectSource(8, srcValue)); 
            
                fTaintLOGICAL(pTmgrTls, resultPtr); 
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr); 
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via OR
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_OR,
                ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))); 
            
            fTaintLOGICAL(pTmgrTls, resultPtr);
            pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
        }
    }
} // sOR_MR<8>

template<> void LOGICAL::sOR_RR<8>
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrTls->isRegisterTainted<8>(regSrcDest);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<8>(regSrc);  

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else
    {
        _LOGTAINT("orRR(8)");
        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0xff => démarquage flags (dest deja non marquée)
            if (destValue == 0xff)  pTmgrTls->unTaintAllFlags();
            // cas 2.2 : destination vaut 0 ; (OR 0, src) équivaut à MOV dest, src
            else if (!destValue) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister(regSrcDest, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via OR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister(regSrcDest, resultPtr); 
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0xff => (OR dest, 0xff) = 0xff, donc démarquer dest et flags
            if (srcValue == 0xff)  
            {
                pTmgrTls->unTaintAllFlags();
                pTmgrTls->unTaintRegister<8>(regSrcDest);
            }
            // cas 3.2 : src vaut 0 => OR dest, 0 ne modifie pas dest => marquage flags avec valeur actuelle destination
            else if (!srcValue) 
            {
                fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(regSrcDest));
            }
            // cas 3.3 : autres valeur de la source => marquage via OR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                    ObjectSource(8, srcValue)); 
                    
                fTaintLOGICAL(pTmgrTls, resultPtr);
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);  
            }                               
        }
        // CAS 4 : source et destination marquées => marquage via OR
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_OR,
                ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)), 
                ObjectSource(pTmgrTls->getRegisterTaint(regSrc))); 

            fTaintLOGICAL(pTmgrTls, resultPtr);
            pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
        }       
    }
} // sOR_RR<8>

///////////////
///// XOR /////
///////////////

// CALLBACKS
void LOGICAL::cXOR(INS &ins) 
{
    // pointeur sur la fonction à appeler (marquage destination)
    void (*callback)() = nullptr;

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {
        if (INS_OperandIsImmediate(ins, 1)) // XOR_IM
        {
            switch (INS_MemoryWriteSize(ins)) // taille de l'opérande mémoire
            {
                case 1: callback = (AFUNPTR) sXOR_IM<8>;  break;
                case 2: callback = (AFUNPTR) sXOR_IM<16>; break;
                case 4: callback = (AFUNPTR) sXOR_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sXOR_IM<64>; break;
                #endif
                default: return; // autres cas non gérés
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYWRITE_EA,
                CALLBACK_DEBUG IARG_END);
        } 
        else  // XOR_RM
        {
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {
                case 1: callback = (AFUNPTR) sXOR_RM<8>;  break;
                case 2: callback = (AFUNPTR) sXOR_RM<16>; break;
                case 4: callback = (AFUNPTR) sXOR_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sXOR_RM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc,
                IARG_MEMORYWRITE_EA,
                CALLBACK_DEBUG IARG_END);
        }
    }
    else // DESTINATION = REGISTRE
    {    
        REG regDest = INS_OperandReg(ins, 0);
        UINT32 regDestSize = getRegSize(regDest);
        
        if (!regDestSize) return;       // registre destination non suivi
        else if (INS_IsMemoryRead(ins)) // XOR_MR
        {
            switch (regDestSize) // taille de l'opérande mémoire
            {
                case 1: callback = (AFUNPTR) sXOR_MR<8>;  break;
                case 2: callback = (AFUNPTR) sXOR_MR<16>; break;
                case 4: callback = (AFUNPTR) sXOR_MR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sOR_MR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA, 
                IARG_UINT32, regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }
        else if (INS_OperandIsImmediate(ins, 1)) // XOR_IR
        {    
            switch (regDestSize) 
            {
                case 1: callback = (AFUNPTR) sXOR_IR<8>; break;
                case 2: callback = (AFUNPTR) sXOR_IR<16>; break;
                case 4: callback = (AFUNPTR) sXOR_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sXOR_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest, 
                IARG_REG_VALUE, regDest,
                CALLBACK_DEBUG IARG_END);
        }
        else // XOR_RR
        {    
            REG regSrc = INS_OperandReg(ins, 1);
            // cas particulier du XOR reg, reg (mise à zero du registre) 
            // => démarquage destination et flags, en FAST_ANALYSIS_CALL
            if (regSrc == regDest) 
            {
                switch (getRegSize(regDest)) 
                {
                case 1: callback = (AFUNPTR) sXOR_RR_EQUAL<8>;  break;
                case 2: callback = (AFUNPTR) sXOR_RR_EQUAL<16>; break;
                case 4: callback = (AFUNPTR) sXOR_RR_EQUAL<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sXOR_RR_EQUAL<32>; break;
                #endif
                }
                INS_InsertCall (ins, IPOINT_BEFORE, callback,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_THREAD_ID,
                    IARG_UINT32, regSrc,
                    CALLBACK_DEBUG IARG_END);
            }
            else
            {
                switch (getRegSize(regSrc)) 
                {
                    case 1: callback = (AFUNPTR) sXOR_RR<8>;  break;
                    case 2: callback = (AFUNPTR) sXOR_RR<16>; break;
                    case 4: callback = (AFUNPTR) sXOR_RR<32>; break;
                    #if TARGET_IA32E
                    case 8: callback = (AFUNPTR) sXOR_RR<64>; break;
                    #endif
                    default: return;
                }
            
                INS_InsertCall (ins, IPOINT_BEFORE, callback,
                    IARG_THREAD_ID,
                    IARG_UINT32,    regSrc,  
                    IARG_REG_VALUE, regSrc,
                    IARG_UINT32,    regDest, 
                    IARG_REG_VALUE, regDest,
                    CALLBACK_DEBUG IARG_END);
            }  
        }
    }
} // cXOR
    
// SIMULATE (spécialisation des templates)
template<> void LOGICAL::sXOR_IM<8>(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if ( !pTmgrGlobal->isMemoryTainted<8>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorIM(8)");
        // XOR x, 0 = x, donc juste marquage flags avec destination
        if (!value) fTaintLOGICAL(pTmgrTls, pTmgrGlobal->getMemoryTaint<8>(writeAddress));
        // CAS 2 : value = 0xff => XOR x, 0xff = NOT x
        else if (value == 0xff) 
        { 
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_NOT,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr);        
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
        }
        // cas général : XOR normal
        else 
        {   
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_XOR,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                ObjectSource(8, value));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr);        
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
        }
    }
} // sXOR_IM<8>

template<> void LOGICAL::sXOR_IR<8>(THREADID tid, ADDRINT value, REG reg, ADDRINT unUsed ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<8>(reg))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorIR(8)");

        // XOR x, 0 = x, donc juste marquage flags avec destination
        if (!value) fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(reg));
        // CAS 2 : value = 0xff => XOR x, 0xff = NOT x
        else if (value == 0xff) 
        { 
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_NOT,
                ObjectSource(pTmgrTls->getRegisterTaint(reg)));
    
            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr); 
            pTmgrTls->updateTaintRegister<8>(reg, resultPtr);       
        }
        else // cas général : XOR normal
        {   
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_XOR,
                ObjectSource(pTmgrTls->getRegisterTaint(reg)),
                ObjectSource(8, value));

            // marquage des flags + dest        
            fTaintLOGICAL(pTmgrTls, resultPtr); 
            pTmgrTls->updateTaintRegister<8>(reg, resultPtr);
        }
    }
} // sXOR_IR<8>

template<> void LOGICAL::sXOR_RM<8>
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{      
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isDestTainted = pTmgrGlobal->isMemoryTainted<8>(writeAddress);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<8>(regSrc);

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorRM(8)");

        // récupération de la valeur de la mémoire
        ADDRINT destValue = getMemoryValue<8>(writeAddress);

        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            TaintBytePtr resultPtr;
            ObjectSource srcReg(pTmgrTls->getRegisterTaint(regSrc));

            // cas 2.1 : destination vaut 0 ; XOR 0, src équivaut à MOV dest, src
            if (!destValue) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
            }
            // cas 2.2 : dest = 0xff ; XOR 0xff, src équivaut à NOT src, affecté à la dest
            else if (destValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via XOR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
            }          
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0 => XOR dest, 0 ne modifie pas dest => marquage flags avec valeur actuelle destination
            if (!srcValue) fTaintLOGICAL(pTmgrTls, pTmgrGlobal->getMemoryTaint<8>(writeAddress));
            // cas 3.2 : src vaut 0xff ; XOR dest, 0xff équivaut à NOT dest
            else if (srcValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)));
                    
                    fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
            }
            // cas 3.3 : autres valeur de la source => marquage via XOR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                    ObjectSource(8, srcValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via XOR
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_XOR,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

            fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, resultPtr);
        }
    }
} // end sXOR_RM<8>

template<> void LOGICAL::sXOR_MR<8>
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrTls->isRegisterTainted<8>(regSrcDest);
    bool isSrcTainted  = pTmgrGlobal->isMemoryTainted<8>(readAddress);  

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorMR(8)");
        // récupération de la valeur de la mémoire
        ADDRINT srcValue = getMemoryValue<8>(readAddress);

        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0 ; (XOR 0, src) équivaut à MOV dest, src
            if (!destValue) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)));  

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 2.2 : dest = 0xff ; (XOR 0xff, src) équivaut à NOT src, affecté à la dest
            else if (destValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)));  

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via XOR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),
                    ObjectSource(8, destValue));  

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted) 
        {
            // cas 3.1 : src vaut 0 ; (XOR dest, 0) ne modifie pas dest => continuer
            if (!srcValue) fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(regSrcDest));
            // cas 3.2 : src vaut 0xff ; (XOR dest, 0xff) équivaut à NOT dest
            else if (srcValue == 0xff)  
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)));  

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 3.3 : autres valeur de la source => marquage via XOR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                    ObjectSource(8, srcValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via XOR
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_XOR,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),  
                ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)));   

            fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
            pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr); 
        }       
    }
} // sXOR_MR<8>

template<> void LOGICAL::sXOR_RR<8>
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isDestTainted = pTmgrTls->isRegisterTainted<8>(regSrcDest);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<8>(regSrc); 

    // CAS 1 : destination et sources non marquées => démarquage flags et quitter
    if (!(isDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();  
    else 
    {
        _LOGTAINT("xorRR(8)");
        // CAS 2 : destination non marquée (et donc source marquée)
        if (!isDestTainted) 
        {
            // cas 2.1 : destination vaut 0 ; (XOR 0, src) équivaut à MOV dest, src
            if (!destValue) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }  
            // cas 2.2 : dest vaut 0xff ; (XOR 0xff, src) équivaut à NOT src, affecté à la dest
            if (destValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 2.3 : autres valeur de la destination => marquage via XOR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),
                    ObjectSource(8, destValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags 
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
        }
        // CAS 3 : source non marquée (et donc destination marquée)
        else if (!isSrcTainted)
        {
            // cas 3.1 : src vaut 0 => XOR dest, 0 ne modifie pas dest
            // => marquage flags avec valeur actuelle destination
            if (!srcValue) fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint(regSrcDest));
            // cas 3.2 : src vaut 0xff; (XOR dest, 0xff) équivaut à NOT dest
            else if (srcValue == 0xff) 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)));  

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }
            // cas 3.3 : autres valeur de la source => marquage via XOR
            else 
            {
                TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)),
                    ObjectSource(8, srcValue));

                fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
                pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
            }                                   
        }
        // CAS 4 : source et destination marquées => marquage via XOR
        else 
        {
            TaintBytePtr resultPtr = std::make_shared<TaintByte>(
                X_XOR,
                ObjectSource(pTmgrTls->getRegisterTaint(regSrc)),  
                ObjectSource(pTmgrTls->getRegisterTaint(regSrcDest)));   

            fTaintLOGICAL(pTmgrTls, resultPtr); // marquage flags
            pTmgrTls->updateTaintRegister<8>(regSrcDest, resultPtr);
        }       
    }
} // sXOR_RR<8>

////////////////
///// TEST /////
////////////////

// CALLBACKS
void LOGICAL::cTEST(INS &ins) 
{	
    void (*callback)() = nullptr;	
    if (INS_OperandIsReg(ins, 0)) // 1ere operande = REGISTRE (IR/MR/RR)
    {
        REG regDest = INS_OperandReg(ins, 0);
        UINT32 regDestSize = getRegSize(regDest);
        
        if (!regDestSize) return;	// registre non instrumenté
        else if (INS_OperandIsImmediate(ins, 1))  // TEST_IR
        {   
            switch (regDestSize) 
            {	
                case 1:	callback = (AFUNPTR) sTEST_IR<8>; break;
                case 2:	callback = (AFUNPTR) sTEST_IR<16>; break;
                case 4:	callback = (AFUNPTR) sTEST_IR<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sTEST_IR<64>; break;
                #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                CALLBACK_DEBUG IARG_END);
        }
        else if (INS_IsMemoryRead(ins)) // TEST_MR
        {			
            switch (regDestSize) 
            {	
            case 1:	callback = (AFUNPTR) sTEST_MR<8>;  break;
            case 2:	callback = (AFUNPTR) sTEST_MR<16>; break;
            case 4:	callback = (AFUNPTR) sTEST_MR<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sTEST_MR<64>; break;
            #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_MEMORYREAD_EA,		// adresse réelle de lecture
                IARG_UINT32, regDest,	// registre destination
                IARG_REG_VALUE, regDest,// valeur lors du callback
                CALLBACK_DEBUG IARG_END);
        }
        else // TEST_RR
        {    
            REG regSrc  = INS_OperandReg(ins, 1);
            if (regSrc == regDest) // cas fréquent : 'test reg, reg' pour tester la nullité 
            {
                switch (regDestSize)
                {
                    case 1:	callback = (AFUNPTR) sTEST_RR_EQUAL<8>;  break;
                    case 2:	callback = (AFUNPTR) sTEST_RR_EQUAL<16>; break;
                    case 4:	callback = (AFUNPTR) sTEST_RR_EQUAL<32>; break;
                    #if TARGET_IA32E
                    case 8: callback = (AFUNPTR) sTEST_RR_EQUAL<64>; break;
                    #endif
                }

                INS_InsertCall (ins, IPOINT_BEFORE, callback,
                    IARG_THREAD_ID,
                    IARG_UINT32, regSrc,		// registre source et dest
                    IARG_REG_VALUE, regSrc,		// valeur lors du callback
                    CALLBACK_DEBUG IARG_END);
            }
            else 
            {
                switch (getRegSize(regSrc)) 
                {	
                    case 1:	callback = (AFUNPTR) sTEST_RR<8>;  break;
                    case 2:	callback = (AFUNPTR) sTEST_RR<16>; break;
                    case 4:	callback = (AFUNPTR) sTEST_RR<32>; break;
                    #if TARGET_IA32E
                    case 8: callback = (AFUNPTR) sTEST_RR<64>; break;
                    #endif
                    default: return;
                }
            
                INS_InsertCall (ins, IPOINT_BEFORE, callback,
                    IARG_THREAD_ID,
                    IARG_UINT32, regSrc,		// registre source
                    IARG_REG_VALUE, regSrc,		// valeur lors du callback
                    IARG_UINT32, regDest,		// registre de destination
                    IARG_REG_VALUE, regDest,	// valeur lors du callback
                    CALLBACK_DEBUG IARG_END);
            }
        }  
    }
    else // 1ere opérande = MEMOIRE (IM/RM)
    {	
        UINT32 memSize = INS_MemoryReadSize(ins);
        if (INS_OperandIsImmediate(ins, 1)) // TEST_IM
        {	
            switch (memSize) // taille de l'opérande mémoire
            {	
                case 1:	callback = (AFUNPTR) sTEST_IM<8>;  break;
                case 2:	callback = (AFUNPTR) sTEST_IM<16>; break;
                case 4:	callback = (AFUNPTR) sTEST_IM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sTEST_IM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_ADDRINT, (ADDRINT) INS_OperandImmediate(ins, 1),
                IARG_MEMORYREAD_EA,
                CALLBACK_DEBUG IARG_END);
        } 
        else // TEST_RM
        { 
            REG regSrc = INS_OperandReg(ins, 1);
            switch (getRegSize(regSrc)) 
            {	
                case 1:	callback = (AFUNPTR) sTEST_RM<8>;  break;
                case 2:	callback = (AFUNPTR) sTEST_RM<16>; break;
                case 4:	callback = (AFUNPTR) sTEST_RM<32>; break;
                #if TARGET_IA32E
                case 8: callback = (AFUNPTR) sTEST_RM<64>; break;
                #endif
                default: return;
            }
            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32, regSrc, 
                IARG_REG_VALUE, regSrc, 
                IARG_MEMORYREAD_EA, 
                CALLBACK_DEBUG IARG_END);
        }
    }
} // cTEST

///////////////
///// NOT /////
///////////////

// CALLBACKS
void LOGICAL::cNOT(INS &ins) 
{
    void (*callback)() = nullptr; // pointeur sur la fonction à appeler

    if (INS_IsMemoryWrite(ins)) // DESTINATION = MEMOIRE
    {   
        switch (INS_MemoryWriteSize(ins)) 
        {   
            case 1: callback = (AFUNPTR) sNOT_M<8>;  break;
            case 2: callback = (AFUNPTR) sNOT_M<16>; break;
            case 4: callback = (AFUNPTR) sNOT_M<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sNOT_M<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_MEMORYWRITE_EA, // l'un des rares cas ou il n'y a pas besoin de THREADID
            CALLBACK_DEBUG IARG_END);
    } 
    else  // DESTINATION = REGISTRE
    {                                 
        REG reg = INS_OperandReg(ins, 0);
        switch (getRegSize(reg)) 
        {
            case 1: callback = (AFUNPTR) sNOT_R<8>;  break;
            case 2: callback = (AFUNPTR) sNOT_R<16>; break;
            case 4: callback = (AFUNPTR) sNOT_R<32>; break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) sNOT_R<64>; break;
            #endif
            default: return;
        }
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32, reg, 
            CALLBACK_DEBUG IARG_END);
    }
} // cNOT

// SIMULATE (spécialisation des templates)
template<> void LOGICAL::sNOT_R<8>(THREADID tid, REG reg ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if (pTmgrTls->isRegisterTainted<8>(reg)) 
    {
        _LOGTAINT("notR(8)");
        pTmgrTls->updateTaintRegister<8>(reg, std::make_shared<TaintByte>(
            X_NOT,
            ObjectSource(pTmgrTls->getRegisterTaint(reg))));
    }
} // sNOT_R<8>
