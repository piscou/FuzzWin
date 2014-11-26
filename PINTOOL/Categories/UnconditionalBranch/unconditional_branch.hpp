
// SIMULATE 
template<UINT32 lengthInBits>
void UNCONDITIONAL_BR::sJMP_M(THREADID tid, ADDRINT effectiveAddress, ADDRINT jumpAddress, ADDRINT insAddress)
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
        _LOGTAINT(tid, insAddress, "JMP_M EA");
        
        // INSERTION CONTRAINTE SUR VALEUR EA différent de effectiveAddress
        g_pFormula->addConstraintAddress(eaPtr, effectiveAddress, insAddress);

        // ne pas oublier d'effacer l'adresse effective :)
        pTmgrTls->clearTaintEffectiveAddress();
    }

    // 2EME TEST : test du marquage de l'adresse de saut
    bool isJumpAddressTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(effectiveAddress);
    if (isJumpAddressTainted)
    {
        _LOGTAINT(tid, insAddress, "JMP_M ADRESSE DE SAUT");
        
        // INSERTION CONTRAINTE SUR VALEUR EA différent de effectiveAddress
        TAINT_OBJECT_PTR addrPtr = pTmgrGlobal->getMemoryTaint<lengthInBits>(effectiveAddress);
        g_pFormula->addConstraintAddress(addrPtr, jumpAddress, insAddress);
    }
}

template<UINT32 lengthInBits>
void UNCONDITIONAL_BR::sJMP_R(THREADID tid, REG reg, ADDRINT jumpAddress, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    //  si registre marquée, insérer une contrainte pour essayer de changer sa valeur
    if (pTmgrTls->isRegisterTainted<lengthInBits>(reg)) 
    {
        _LOGTAINT(tid, insAddress, "JMP_R REGISTRE");

        // INSERTION CONTRAINTE SUR VALEUR REGISTRE
        TAINT_OBJECT_PTR regPtr = pTmgrTls->getRegisterTaint<lengthInBits>(reg, jumpAddress);
        g_pFormula->addConstraintAddress(regPtr, jumpAddress, insAddress);
    }
}