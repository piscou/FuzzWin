template<UINT32 lengthInBits> 
void CALL::sCALL_M(THREADID tid, bool isFarCall, ADDRINT effectiveAddress, ADDRINT jumpAddress, ADDRINT stackValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // récupération de l'adresse effective
#if TARGET_IA32
    TaintDwordPtr eaPtr = pTmgrTls->getTaintEffectiveAddress();
#else
    TaintQwordPtr eaPtr = pTmgrTls->getTaintEffectiveAddress();
#endif

    // 1ER TEST : si adresse effective marquée, insérer une contrainte pour essayer de la changer
    if (eaPtr) 
    {
        _LOGTAINT(tid, insAddress, "CALL_M EA");
        
        // INSERTION CONTRAINTE SUR VALEUR EA différent de effectiveAddress
        g_pFormula->addConstraintAddress(eaPtr, effectiveAddress, insAddress);

        // ne pas oublier d'effacer l'adresse effective :)
        pTmgrTls->clearTaintEffectiveAddress();
    }
    
    // 2EME TEST : test du marquage de l'adresse de saut
    bool isJumpAddressTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(effectiveAddress);
    if (isJumpAddressTainted)
    {
        _LOGTAINT(tid, insAddress, "CALL_M ADRESSE DE SAUT");
        
        // INSERTION CONTRAINTE SUR VALEUR EA différent de effectiveAddress
        TAINT_OBJECT_PTR addrPtr = pTmgrGlobal->getMemoryTaint<lengthInBits>(effectiveAddress);
        g_pFormula->addConstraintAddress(addrPtr, jumpAddress, insAddress);
    }

    // effet de CALL : pousser l'adresse EIP sur la pile (+ CS si CALL FAR)
    // équivalent à un PUSH valeur (EIP et CS ne sont pas suivis en marquage)
    // le PUSH décrémente ESP/RSP de 'lengthInBits >> 3' + 2 octets si CALL FAR

    ADDRINT pushedLength = lengthInBits >> 3;
    if (isFarCall) pushedLength += 2;

#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP - (longueur pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackValue)),
            ObjectSource(32, pushedLength)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = RSP - (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackValue)),
            ObjectSource(64, pushedLength)));
    }
#endif

    ADDRINT startAddress = stackValue - pushedLength;
    while (startAddress < stackValue)
    {
        pTmgrGlobal->unTaintMemory<8>(startAddress);
        ++startAddress;
    }
}

template<UINT32 lengthInBits> 
void CALL::sCALL_R(THREADID tid, bool isFarCall, REG reg, ADDRINT jumpAddress, ADDRINT stackValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    //  si registre marquée, insérer une contrainte pour essayer de changer sa valeur
    if (pTmgrTls->isRegisterTainted<lengthInBits>(reg)) 
    {
        _LOGTAINT(tid, insAddress, "CALL_R REGISTRE");
        
        // INSERTION CONTRAINTE SUR VALEUR REGISTRE
        TAINT_OBJECT_PTR regPtr = pTmgrTls->getRegisterTaint<lengthInBits>(reg, jumpAddress);
        g_pFormula->addConstraintAddress(regPtr, jumpAddress, insAddress);
    }

    // effet de CALL : pousser l'adresse EIP sur la pile (+ CS si CALL FAR)
    // équivalent à un PUSH valeur (EIP et CS ne sont pas suivis en marquage)
    // le PUSH décrémente ESP/RSP de 'lengthInBits >> 3' + 2 octets si CALL FAR

    ADDRINT pushedLength = lengthInBits >> 3;
    if (isFarCall) pushedLength += 2;

#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP - (longueur pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackValue)),
            ObjectSource(32, pushedLength)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = RSP - (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackValue)),
            ObjectSource(64, pushedLength)));
    }
#endif

    // démarquage de la pile : pushedLength octets à partir de stackValue - pushedLength
    ADDRINT startAddress = stackValue - pushedLength;
    while (startAddress < stackValue)
    {
        pTmgrGlobal->unTaintMemory<8>(startAddress);
        ++startAddress;
    }
}
