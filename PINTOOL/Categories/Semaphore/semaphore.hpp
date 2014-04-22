template<UINT32 lengthInBits> void SEMAPHORE::sCMPXCHG_RM
    (THREADID tid, REG regSrc, ADDRINT address, REG cmpReg, ADDRINT cmpRegValue, ADDRINT insAddress)
{
    // 1ere partie de CMPXCHG : il s'agit en fait d'un CMP_RM
    // donc appeler la fonction correspondante implémentée dans BINARY
    // qui marquera les flags en conséquence
    BINARY::sCMP_RM<lengthInBits>(tid, cmpReg, cmpRegValue, address ,insAddress);

    // 2ème partie de CMPXCHG
    // si opérandes sont égales : MOV regSrc->Memoire
    // sinon                      MOV Mémoire -> cmpReg (AL..RAX)
    ADDRINT addressValue = getMemoryValue<lengthInBits>(address);
    if (addressValue == cmpRegValue)   DATAXFER::sMOV_RM<lengthInBits>(tid, regSrc, address ,insAddress);
    else                               DATAXFER::sMOV_MR<lengthInBits>(tid, address, cmpReg ,insAddress);
} // sCMPXCHG_RM

template<UINT32 lengthInBits> void SEMAPHORE::sCMPXCHG_RR
    (THREADID tid, REG regSrc, REG regDest, ADDRINT regDestValue, REG cmpReg, ADDRINT cmpRegValue, ADDRINT insAddress)
{
    // 1ere partie de CMPXCHG : il s'agit en fait d'un CMP_RR
    // donc appeler la fonction correspondante implémentée dans BINARY
    // qui marquera les flags en conséquence
    BINARY::sCMP_RR<lengthInBits>(tid, cmpReg, cmpRegValue, regDest, regDestValue ,insAddress);

    // 2ème partie de CMPXCHG
    // si opérandes sont égales : MOV regSrc->Memoire
    // sinon                      MOV RegDest -> cmpReg (AL..RAX)
    if (regDestValue == cmpRegValue)   DATAXFER::sMOV_RR<lengthInBits>(tid, regSrc, regDest ,insAddress);
    else                               DATAXFER::sMOV_RR<lengthInBits>(tid, regDest, cmpReg ,insAddress);
} // sCMPXCHG_RR

template<UINT32 lengthInBits>
void SEMAPHORE::sXADD_R(THREADID tid, REG regSrc, ADDRINT regSrcValue, 
                        REG regDest, ADDRINT regDestValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);
    bool isRegDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regDest);

    if (! (isRegSrcTainted || isRegDestTainted)) pTmgrTls->unTaintAllFlags();
    else
    {
        // addition src + dest, puis stockage dans variable temporaire
        _LOGTAINT(tid, insAddress, "XADD_R" + decstr(lengthInBits));

        ObjectSource objSrc = (isRegSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);

        ObjectSource objSrcDest = (isRegDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regDest, regDestValue))
            : ObjectSource(lengthInBits, regDestValue);
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // déplacement destination -> source
        REGINDEX regIndexSrc  = getRegIndex(regSrc);
        REGINDEX regIndexDest = getRegIndex(regDest);
        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart) 
        {	
            if (pTmgrTls->isRegisterPartTainted(regIndexDest, regPart))   
            {
                pTmgrTls->updateTaintRegisterPart(regIndexSrc, regPart, std::make_shared<TaintByte>(
                    X_ASSIGN, 
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndexDest, regPart))));
            }
            else pTmgrTls->unTaintRegisterPart(regIndexSrc, regPart);
        }

        // affectation du resultat de l'addition à la destination, et marquage flags
        BINARY::fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<lengthInBits>(regDest, resultPtr);
    }
} // sXADD_R

template<UINT32 lengthInBits>
void SEMAPHORE::sXADD_M(THREADID tid, REG regSrc, ADDRINT regSrcValue,
                        ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);
    bool isMemTainted     = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);

    if (! (isRegSrcTainted || isMemTainted)) pTmgrTls->unTaintAllFlags();
    else
    {
        // addition src + dest, puis stockage dans variable temporaire
        _LOGTAINT(tid, insAddress, "XADD_M" + decstr(lengthInBits));

        ObjectSource objSrc = (isRegSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);

        ObjectSource objSrcDest = (isMemTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // déplacement destination -> source
        REGINDEX regIndexSrc  = getRegIndex(regSrc);
        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart, ++writeAddress) 
        {	
            if (pTmgrGlobal->isMemoryTainted<8>(writeAddress))   
            {
                pTmgrTls->updateTaintRegisterPart(regIndexSrc, regPart, std::make_shared<TaintByte>(
                    X_ASSIGN, 
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress))));
            }
            else pTmgrTls->unTaintRegisterPart(regIndexSrc, regPart);
        }

        // affectation du resultat de l'addition à la destination, et marquage flags
        BINARY::fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrc, resultPtr);
    }

} // sXADD_M

