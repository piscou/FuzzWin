/////////
// NEG //
/////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sNEG_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))  pTmgrTls->unTaintAllFlags(); // OSZAPC
    else 
    {
        _LOGTAINT("negM" << lengthInBits);
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));

        // création de l'objet résultat
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_NEG,
            objSrc);

        // marquage flags et destination
        fTaintNEG(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sNEG_M

template<UINT32 lengthInBits> void BINARY::sNEG_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg)) pTmgrTls->unTaintAllFlags(); // OSZAPC
    else 
    {
        _LOGTAINT("negR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));

        // création de l'objet résultat
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_NEG,
            objSrc);

        // marquage flags et destination
        fTaintNEG(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sNEG_R

/////////
// INC //
/////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sINC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("incM");
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        
        // création de l'objet résultat
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_INC,
            objSrc);

        // marquage flags et destination
        fTaintINC(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sINC_M

template<UINT32 lengthInBits> void BINARY::sINC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg)) fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("incR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        
        // création de l'objet résultat
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_INC,
            objSrc);

        // marquage flags et destination
        fTaintINC(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sINC_R

/////////
// DEC //
/////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sDEC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))  fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("decM");
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));

        // création de l'objet résultat
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_DEC,
            objSrc);

        // marquage flags et destination
        fTaintDEC(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sDEC_M

template<UINT32 lengthInBits> void BINARY::sDEC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg))  fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("decR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        
        // création de l'objet résultat
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_DEC,
            objSrc);

        // marquage flags et destination
        fTaintDEC(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sDEC_R

/////////
// ADD //
/////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sADD_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addIR" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        ObjectSource objSrc(lengthInBits, value);		
    
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);			
    }
} // sADD_IR

template<UINT32 lengthInBits> void BINARY::sADD_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addIM" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        ObjectSource objSrc(lengthInBits, value);		
    
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sADD_IM

template<UINT32 lengthInBits> 
void BINARY::sADD_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addMR" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
            : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));

        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et dest
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }
} // sADD_MR

template<UINT32 lengthInBits> 
void BINARY::sADD_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addRM" << lengthInBits << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);

        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sADD_RM

template<UINT32 lengthInBits> void BINARY::sADD_RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addRR" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
                ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
                : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted)
                ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
                : ObjectSource(lengthInBits, regSrcValue);
    
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }
} // sADD_RR

/////////
// SUB //
/////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sSUB_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subIR" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        ObjectSource objSrc(lengthInBits, value);		
    
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);			
    }
} // sSUB_IR

template<UINT32 lengthInBits> void BINARY::sSUB_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subIM" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        ObjectSource objSrc(lengthInBits, value);		
    
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sSUB_IM

template<UINT32 lengthInBits> 
void BINARY::sSUB_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subMR" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
            : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));

        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et dest
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }
} // sSUB_MR

template<UINT32 lengthInBits> 
void BINARY::sSUB_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subRM" << lengthInBits << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);

        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sSUB_RM

template<UINT32 lengthInBits> void BINARY::sSUB_RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subRR" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
                ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
                : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted)
                ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
                : ObjectSource(lengthInBits, regSrcValue);
    
        std::shared_ptr<TaintObject<lengthInBits>> resultPtr = std::make_shared<TaintObject<lengthInBits>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }
} // sSUB_RR

/////////
// CMP //
/////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sCMP_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpIR" << lengthInBits << " ");

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue)), ObjectSource(lengthInBits, value));			
    }
} // sCMP_IR

template<UINT32 lengthInBits> void BINARY::sCMP_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpIM" << lengthInBits << " ");

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)), ObjectSource(lengthInBits, value));					
    }
} // sCMP_IM

template<UINT32 lengthInBits> 
void BINARY::sCMP_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpMR" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
            : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, objSrcDest, objSrc);	
    }
} // sCMP_MR

template<UINT32 lengthInBits> 
void BINARY::sCMP_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpRM" << lengthInBits << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, objSrcDest, objSrc);	
    }
} // sCMP_RM

template<UINT32 lengthInBits> void BINARY::sCMP_RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpRR" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
                ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
                : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted)
                ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
                : ObjectSource(lengthInBits, regSrcValue);
    
        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, objSrcDest, objSrc);   	
    }
} // sCMP_RR

// FLAGS
template<UINT32 lengthInBits> void BINARY::fTaintCMP
    (TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, const ObjectSource &objSrc) 
{
    ObjectSource objResult(std::make_shared<TaintObject<lengthInBits>>(
        X_SUB,
        objSrcDest,
        objSrc));
    
    // CMP : O/S/Z/A/P/C
    pTmgrTls->updateTaintCarryFlag (std::make_shared<TaintBit>(F_CARRY_SUB, objSrcDest, objSrc));
    pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objResult));
    pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AUXILIARY_SUB, objSrcDest, objSrc));
    pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_ARE_EQUAL, objSrcDest, objSrc));
    pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objResult));
    pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_SUB, objSrcDest, objSrc, objResult));
} // fTaintCMP

//////////
// IMUL //
//////////

// SIMULATE
template<UINT32 lengthInBits> void BINARY::sIMUL_1M
    (THREADID tid, ADDRINT readAddress, ADDRINT implicitRegValue ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<lengthInBits>::getReg(); // 1ere opérande et registre destination partie basse (AL/AX/EAX/RAX)
    REG regIO  = registerIO<lengthInBits>::getReg();  // registre de destination, partie haute (AH, DX, EDX, RDX)
   
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regACC);
    bool isSrcTainted =	pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted)) 
    {
        // démarquage flags et partie haute dest (partie basse déjà non marquée)                       
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();	  
        pTmgrTls->unTaintRegister<lengthInBits>(regIO);
    }	
    else 
    {
        _LOGTAINT("imul1M" << lengthInBits << " ");
        	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regACC, implicitRegValue))
            : ObjectSource(lengthInBits, implicitRegValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));
        
        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*lengthInBits)>> resultPtr = std::make_shared<TaintObject<(2*lengthInBits)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	

        // marquage destination : à partir du resultat, il faut extraire
        // --les (lengthInBits>>3) octets faibles -> registre d'accumulation (AL/AX/EAX/RAX)
        // --les (lengthInBits>>3) octets forts   -> registre d'I/O (AH/DX/EDX/RDX)
        REGINDEX regIndexes[2] = { getRegIndex(regACC), getRegIndex(regIO) };
        UINT32 indexOfExtraction = 0;
        ObjectSource objResult(resultPtr);
        
        for (UINT32 index = 0 ; index < 2 ; ++index)
        {
            REGINDEX regIndex = regIndexes[index]; // partie basse puis partie haute
            for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart, ++indexOfExtraction)
            {
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    EXTRACT,
                    objResult,
                    ObjectSource(8, indexOfExtraction)));
            }
        }
    }
} // sIMUL_1M

template<UINT32 lengthInBits> void BINARY::sIMUL_1R
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT implicitRegValue ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<lengthInBits>::getReg(); // 1ere opérande et registre destination partie basse (AL/AX/EAX/RAX)
    REG regIO  = registerIO<lengthInBits>::getReg();  // registre de destination, partie haute (AH, DX, EDX, RDX)
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regACC);
    bool isSrcTainted =	pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);
    

    if ( !(isSrcDestTainted || isSrcTainted)) 
    {
        // démarquage flags et partie haute dest (partie basse non marquée)
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();	  
        pTmgrTls->unTaintRegister<lengthInBits>(regIO);
    }	
    else 
    {
        _LOGTAINT("imul1R" << lengthInBits << " ");

        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regACC, implicitRegValue))
            : ObjectSource(lengthInBits, implicitRegValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);
        
        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*lengthInBits)>> resultPtr = std::make_shared<TaintObject<(2*lengthInBits)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	

        // marquage destination : à partir du resultat, il faut extraire
        // --les (lengthInBits>>3) octets faibles -> registre d'accumulation (AL/AX/EAX/RAX)
        // --les (lengthInBits>>3) octets forts   -> registre d'I/O (AH/DX/EDX/RDX)
        REGINDEX regIndexes[2] = { getRegIndex(regACC), getRegIndex(regIO) };
        UINT32 indexOfExtraction = 0;
        ObjectSource objResult(resultPtr);
        
        for (UINT32 index = 0 ; index < 2 ; ++index)
        {
            REGINDEX regIndex = regIndexes[index]; // partie basse puis partie haute
            for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart, ++indexOfExtraction)
            {
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    EXTRACT,
                    objResult,
                    ObjectSource(8, indexOfExtraction)));
            }
        }
    }
} // sIMUL_1R

template<UINT32 lengthInBits> void BINARY::sIMUL_2MR
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // IMUL2MR <=> regSrcDest = mem * regSrcDest
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))
    {
        // démarquage flags (destination déja démarquée)
        pTmgrTls->unTaintCarryFlag();  	
        pTmgrTls->unTaintOverflowFlag();	 
    }
    else 
    {
        _LOGTAINT("imul2MR" << lengthInBits << " ");
        
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
            : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));

        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*lengthInBits)>> resultPtr = std::make_shared<TaintObject<(2*lengthInBits)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "lengthInBits" objects de taille 8bits à partir du résultat de longueur lengthInBits*2
        REGINDEX regIndex = getRegIndex(regSrcDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_2MR

template<UINT32 lengthInBits> void BINARY::sIMUL_2RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // IMUL2RR <=> regSrcDest = regSrc * regSrcDest
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted)) 
    {
        // démarquage flags (destination déja démarquée)
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();		
    }
    else 
    {
        _LOGTAINT("imul2RR" << lengthInBits << " ");
 
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue))
            : ObjectSource(lengthInBits, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);
        
        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*lengthInBits)>> resultPtr = std::make_shared<TaintObject<(2*lengthInBits)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "lengthInBits" objects de taille 8bits à partir du résultat de longueur lengthInBits*2
        REGINDEX regIndex = getRegIndex(regSrcDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_2RR

template<UINT32 lengthInBits> 
void BINARY::sIMUL_3M(THREADID tid, ADDRINT value, ADDRINT readAddress, REG regDest ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if (!pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();    
        pTmgrTls->unTaintRegister<lengthInBits>(regDest);
    }			
    else 
    {
        _LOGTAINT("imul3IM" << lengthInBits << " ");

        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*lengthInBits)>> resultPtr = std::make_shared<TaintObject<(2*lengthInBits)>>(
            X_IMUL,
            ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress)),
            ObjectSource(lengthInBits, value));

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "lengthInBits" objects de taille 8bits à partir du résultat de longueur lengthInBits*2
        REGINDEX regIndex = getRegIndex(regDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_3M

template<UINT32 lengthInBits> 
void BINARY::sIMUL_3R(THREADID tid, ADDRINT value, REG regSrc, ADDRINT regSrcValue, REG regDest ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if (!pTmgrTls->isRegisterTainted<lengthInBits>(regSrc)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
        pTmgrTls->unTaintRegister<lengthInBits>(regDest);
    }			
    else 
    {
        _LOGTAINT("imul3IR" << lengthInBits << " ");

        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*lengthInBits)>> resultPtr = std::make_shared<TaintObject<(2*lengthInBits)>>(
            X_IMUL,
            ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue)),
            ObjectSource(lengthInBits, value));

        // marquage des flags (uniquement besoin du résultat) 
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "lengthInBits" objects de taille 8bits à partir du résultat de longueur lengthInBits*2
        REGINDEX regIndex = getRegIndex(regDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_3R

////////////////////////////
// DIVISION (DIV et IDIV) //
////////////////////////////

// SIMULATE
 template<UINT32 lengthInBits> void BINARY::sDIVISION_M(THREADID tid, ADDRINT readAddress, 
    bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG)
{
    // dividende = registre (lengthInBits*2 bits, composé), diviseur = mémoire (lengthInBits bits)
    // partie faible du dividende = registre d'accumulation (AL/AX/EAX/RAX)
    // partie forte du dividende = registre d'I/O (AH/DX/EDX/RDX)
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<lengthInBits>::getReg(); 
    REG regIO  = registerIO<lengthInBits>::getReg();  
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isDivisorTainted =      pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);
    bool isLowDividendTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(regACC);
    bool isHighDividendTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regIO);
    
    if (isLowDividendTainted || isHighDividendTainted || isDivisorTainted) 
    {
        _LOGTAINT(((isSignedDivision) ? "I" : "") << "DIVM " << lengthInBits << " " );

        ObjectSource objSrcLowDividend = (isLowDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regACC, lowDividendValue))
            : ObjectSource(lengthInBits, lowDividendValue);

        ObjectSource objSrcHighDividend = (isHighDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regIO, highDividendValue))
            : ObjectSource(lengthInBits, highDividendValue);
  
        ObjectSource objSrcDivisor = (isDivisorTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));

        // création de l'objet correspondant au quotient
        TaintObject<lengthInBits> quotient(
            (isSignedDivision) ? X_IDIV_QUO : X_DIV_QUO, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);
        
        // création de l'objet correspondant au reste
        TaintObject<lengthInBits> remainder(
            (isSignedDivision) ? X_IDIV_REM : X_DIV_REM, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);

        // Affectation quotient et reste aux registres adéquats (idem dividende, cf manuel Intel)
        pTmgrTls->updateTaintRegister<lengthInBits>(regACC, std::make_shared<TaintObject<lengthInBits>>(quotient));
        pTmgrTls->updateTaintRegister<lengthInBits>(regIO,  std::make_shared<TaintObject<lengthInBits>>(remainder));	
    }
} // sDIVISION_M

template<UINT32 lengthInBits> void BINARY::sDIVISION_R(THREADID tid, REG regSrc, ADDRINT regSrcValue, 
    bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG)
{
    // dividende = registre (lengthInBits*2 bits, composé), diviseur = mémoire (lengthInBits bits)
    // partie faible du dividende = registre d'accumulation (AL/AX/EAX/RAX)
    // partie forte du dividende = registre d'I/O (AH/DX/EDX/RDX)
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<lengthInBits>::getReg(); 
    REG regIO  = registerIO<lengthInBits>::getReg();  
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isDivisorTainted      = pTmgrTls->isRegisterTainted<lengthInBits>(regSrc, regSrcValue);
    bool isLowDividendTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(regACC);
    bool isHighDividendTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regIO);
    
    if (isLowDividendTainted || isLowDividendTainted || isDivisorTainted) 
    {
        _LOGTAINT(((isSignedDivision) ? "I" : "") << "DIVR " << lengthInBits << " " );

        ObjectSource objSrcLowDividend = (isLowDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regACC, lowDividendValue))
            : ObjectSource(lengthInBits, lowDividendValue);

        ObjectSource objSrcHighDividend = (isHighDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regIO, highDividendValue))
            : ObjectSource(lengthInBits, highDividendValue);

        ObjectSource objSrcDivisor = (isDivisorTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);
         
        // création de l'objet correspondant au quotient
        TaintObject<lengthInBits> quotient(
            (isSignedDivision) ? X_IDIV_QUO : X_DIV_QUO, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);
        
        // création de l'objet correspondant au reste
        TaintObject<lengthInBits> remainder(
            (isSignedDivision) ? X_IDIV_REM : X_DIV_REM, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);

        // Affectation quotient et reste aux registres adéquats (idem dividende, cf manuel Intel)
        pTmgrTls->updateTaintRegister<lengthInBits>(regACC, std::make_shared<TaintObject<lengthInBits>>(quotient));
        pTmgrTls->updateTaintRegister<lengthInBits>(regIO,  std::make_shared<TaintObject<lengthInBits>>(remainder));	
    }
} //sDIVISION_R