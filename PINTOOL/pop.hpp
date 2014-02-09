template<UINT32 len> 
void POP::sPOP_M(THREADID tid, ADDRINT writeAddress, ADDRINT stackAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    ADDRINT savedStackAddress = stackAddress; // elle servira pour le test du marquage ESP

    if ( !pTmgrGlobal->isMemoryTainted<len>(stackAddress)) pTmgrGlobal->unTaintMemory<len>(writeAddress); 
    else 
    {
        _LOGTAINT("popM" << len);
        
        ADDRINT endAddress = stackAddress + (len >> 3);   // adresse de fin de traitement (exclue)
        do  
        {
            if (pTmgrGlobal->isMemoryTainted<8>(stackAddress))  
            {
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddress))));
            }
            else pTmgrGlobal->unTaintMemory<8>(writeAddress);
            ++writeAddress;
        } while (++stackAddress < endAddress); 
    }

    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP + (longueur popée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, savedStackAddress)),
            ObjectSource(32, len >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = ESP + (longueur popée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, savedStackAddress)),
            ObjectSource(64, len >> 3)));
    }
#endif

} // sPOP_M

template<UINT32 len> 
void POP::sPOP_R(THREADID tid, REG regDest, ADDRINT stackAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    ADDRINT savedStackAddress = stackAddress; // elle servira pour le test du marquage ESP

    if ( !pTmgrGlobal->isMemoryTainted<len>(stackAddress)) pTmgrTls->unTaintRegister<len>(regDest); 
    else 
    {
        // copier coller de la procédure MOVMR<len>
        REGINDEX regIndex = getRegIndex(regDest);
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart, ++stackAddress)
        {
            if (pTmgrGlobal->isMemoryTainted<8>(stackAddress))  // octet marqué ? 
            {	
                _LOGTAINT("POPR" << len << " octet " << regPart);	
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    X_ASSIGN, 
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddress))));
            }
            else pTmgrTls->unTaintRegisterPart(regIndex, regPart);
        }
    }

    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP + (longueur popée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, savedStackAddress)),
            ObjectSource(32, len >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = ESP + (longueur popée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, savedStackAddress)),
            ObjectSource(64, len >> 3)));
    }
#endif

} // sPOP_R