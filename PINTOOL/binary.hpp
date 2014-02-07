/////////
// NEG //
/////////

// SIMULATE
template<UINT32 len> void BINARY::sNEG_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress))  pTmgrTls->unTaintAllFlags(); // OSZAPC
    else 
    {
        _LOGTAINT("negM" << len);
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<len>(writeAddress));

        // création de l'objet résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_NEG,
            objSrc);

        // marquage flags et destination
        fTaintNEG(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sNEG_M

template<UINT32 len> void BINARY::sNEG_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags(); // OSZAPC
    else 
    {
        _LOGTAINT("negR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<len>(reg, regValue));

        // création de l'objet résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_NEG,
            objSrc);

        // marquage flags et destination
        fTaintNEG(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sNEG_R

/////////
// INC //
/////////

// SIMULATE
template<UINT32 len> void BINARY::sINC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress)) fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("incM");
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<len>(writeAddress));
        
        // création de l'objet résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_INC,
            objSrc);

        // marquage flags et destination
        fTaintINC(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sINC_M

template<UINT32 len> void BINARY::sINC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<len>(reg)) fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("incR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        
        // création de l'objet résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_INC,
            objSrc);

        // marquage flags et destination
        fTaintINC(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sINC_R

/////////
// DEC //
/////////

// SIMULATE
template<UINT32 len> void BINARY::sDEC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress))  fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("decM");
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<len>(writeAddress));

        // création de l'objet résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_DEC,
            objSrc);

        // marquage flags et destination
        fTaintDEC(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sDEC_M

template<UINT32 len> void BINARY::sDEC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<len>(reg))  fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("decR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        
        // création de l'objet résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_DEC,
            objSrc);

        // marquage flags et destination
        fTaintDEC(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sDEC_R

/////////
// ADD //
/////////

// SIMULATE
template<UINT32 len> void BINARY::sADD_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<len>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addIR" << len << " ");

        ObjectSource objSrcDest(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        ObjectSource objSrc(len, value);		
    
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);			
    }
} // sADD_IR

template<UINT32 len> void BINARY::sADD_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addIM" << len << " ");

        ObjectSource objSrcDest(pTmgrGlobal->getMemoryTaint<len>(writeAddress));
        ObjectSource objSrc(len, value);		
    
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);			
    }
} // sADD_IM

template<UINT32 len> 
void BINARY::sADD_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<len>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addMR" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, getMemoryValue<len>(readAddress));

        shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et dest
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);			
    }
} // sADD_MR

template<UINT32 len> 
void BINARY::sADD_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addRM" << len << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);

        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);			
    }
} // sADD_RM

template<UINT32 len> void BINARY::sADD_RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addRR" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
                ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
                : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted)
                ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
                : ObjectSource(len, regSrcValue);
    
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_ADD,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);			
    }
} // sADD_RR

/////////
// SUB //
/////////

// SIMULATE
template<UINT32 len> void BINARY::sSUB_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<len>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subIR" << len << " ");

        ObjectSource objSrcDest(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        ObjectSource objSrc(len, value);		
    
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);			
    }
} // sSUB_IR

template<UINT32 len> void BINARY::sSUB_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subIM" << len << " ");

        ObjectSource objSrcDest(pTmgrGlobal->getMemoryTaint<len>(writeAddress));
        ObjectSource objSrc(len, value);		
    
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);			
    }
} // sSUB_IM

template<UINT32 len> 
void BINARY::sSUB_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<len>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subMR" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, getMemoryValue<len>(readAddress));

        shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et dest
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);			
    }
} // sSUB_MR

template<UINT32 len> 
void BINARY::sSUB_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subRM" << len << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);

        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);			
    }
} // sSUB_RM

template<UINT32 len> void BINARY::sSUB_RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subRR" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
                ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
                : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted)
                ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
                : ObjectSource(len, regSrcValue);
    
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);			
    }
} // sSUB_RR

/////////
// CMP //
/////////

// SIMULATE
template<UINT32 len> void BINARY::sCMP_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrTls->isRegisterTainted<len>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpIR" << len << " ");

        // marquage flags
        fTaintCMP<len>(pTmgrTls, ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue)), ObjectSource(len, value));			
    }
} // sCMP_IR

template<UINT32 len> void BINARY::sCMP_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpIM" << len << " ");

        // marquage flags
        fTaintCMP<len>(pTmgrTls, ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)), ObjectSource(len, value));					
    }
} // sCMP_IM

template<UINT32 len> 
void BINARY::sCMP_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<len>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpMR" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, getMemoryValue<len>(readAddress));

        // marquage flags
        fTaintCMP<len>(pTmgrTls, objSrcDest, objSrc);	
    }
} // sCMP_MR

template<UINT32 len> 
void BINARY::sCMP_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpRM" << len << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);

        // marquage flags
        fTaintCMP<len>(pTmgrTls, objSrcDest, objSrc);	
    }
} // sCMP_RM

template<UINT32 len> void BINARY::sCMP_RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpRR" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted) 
                ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
                : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted)
                ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
                : ObjectSource(len, regSrcValue);
    
        // marquage flags
        fTaintCMP<len>(pTmgrTls, objSrcDest, objSrc);   	
    }
} // sCMP_RR

// FLAGS
template<UINT32 len> void BINARY::fTaintCMP
    (TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, const ObjectSource &objSrc) 
{
    ObjectSource objResult(std::make_shared<TaintObject<len>>(
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
template<UINT32 len> void BINARY::sIMUL_1M
    (THREADID tid, ADDRINT readAddress, ADDRINT implicitRegValue ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<len>::getReg(); // 1ere opérande et registre destination partie basse (AL/AX/EAX/RAX)
    REG regIO  = registerIO<len>::getReg();  // registre de destination, partie haute (AH, DX, EDX, RDX)
   
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regACC);
    bool isSrcTainted =	pTmgrGlobal->isMemoryTainted<len>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted)) 
    {
        // démarquage flags et partie haute dest (partie basse déjà non marquée)                       
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();	  
        pTmgrTls->unTaintRegister<len>(regIO);
    }	
    else 
    {
        _LOGTAINT("imul1M" << len << " ");
        	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regACC, implicitRegValue))
            : ObjectSource(len, implicitRegValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, getMemoryValue<len>(readAddress));
        
        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*len)>> resultPtr = std::make_shared<TaintObject<(2*len)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	

        // marquage destination : à partir du resultat, il faut extraire
        // --les (len>>3) octets faibles -> registre d'accumulation (AL/AX/EAX/RAX)
        // --les (len>>3) octets forts   -> registre d'I/O (AH/DX/EDX/RDX)
        REGINDEX regIndexes[2] = { getRegIndex(regACC), getRegIndex(regIO) };
        UINT32 indexOfExtraction = 0;
        ObjectSource objResult(resultPtr);
        
        for (UINT32 index = 0 ; index < 2 ; ++index)
        {
            REGINDEX regIndex = regIndexes[index]; // partie basse puis partie haute
            for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart, ++indexOfExtraction)
            {
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    EXTRACT,
                    objResult,
                    ObjectSource(8, indexOfExtraction)));
            }
        }
    }
} // sIMUL_1M

template<UINT32 len> void BINARY::sIMUL_1R
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT implicitRegValue ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<len>::getReg(); // 1ere opérande et registre destination partie basse (AL/AX/EAX/RAX)
    REG regIO  = registerIO<len>::getReg();  // registre de destination, partie haute (AH, DX, EDX, RDX)
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regACC);
    bool isSrcTainted =	pTmgrTls->isRegisterTainted<len>(regSrc);
    

    if ( !(isSrcDestTainted || isSrcTainted)) 
    {
        // démarquage flags et partie haute dest (partie basse non marquée)
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();	  
        pTmgrTls->unTaintRegister<len>(regIO);
    }	
    else 
    {
        _LOGTAINT("imul1R" << len << " ");

        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regACC, implicitRegValue))
            : ObjectSource(len, implicitRegValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*len)>> resultPtr = std::make_shared<TaintObject<(2*len)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	

        // marquage destination : à partir du resultat, il faut extraire
        // --les (len>>3) octets faibles -> registre d'accumulation (AL/AX/EAX/RAX)
        // --les (len>>3) octets forts   -> registre d'I/O (AH/DX/EDX/RDX)
        REGINDEX regIndexes[2] = { getRegIndex(regACC), getRegIndex(regIO) };
        UINT32 indexOfExtraction = 0;
        ObjectSource objResult(resultPtr);
        
        for (UINT32 index = 0 ; index < 2 ; ++index)
        {
            REGINDEX regIndex = regIndexes[index]; // partie basse puis partie haute
            for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart, ++indexOfExtraction)
            {
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    EXTRACT,
                    objResult,
                    ObjectSource(8, indexOfExtraction)));
            }
        }
    }
} // sIMUL_1R

template<UINT32 len> void BINARY::sIMUL_2MR
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    // IMUL2MR <=> regSrcDest = mem * regSrcDest
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<len>(readAddress);

    if ( !(isSrcDestTainted || isSrcTainted))
    {
        // démarquage flags (destination déja démarquée)
        pTmgrTls->unTaintCarryFlag();  	
        pTmgrTls->unTaintOverflowFlag();	 
    }
    else 
    {
        _LOGTAINT("imul2MR" << len << " ");
        
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, getMemoryValue<len>(readAddress));

        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*len)>> resultPtr = std::make_shared<TaintObject<(2*len)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "len" objects de taille 8bits à partir du résultat de longueur len*2
        REGINDEX regIndex = getRegIndex(regSrcDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_2MR

template<UINT32 len> void BINARY::sIMUL_2RR
    (THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    // IMUL2RR <=> regSrcDest = regSrc * regSrcDest
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<len>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted)) 
    {
        // démarquage flags (destination déja démarquée)
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();		
    }
    else 
    {
        _LOGTAINT("imul2RR" << len << " ");
 
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*len)>> resultPtr = std::make_shared<TaintObject<(2*len)>>(
            X_IMUL,
            objSrcDest,
            objSrc);

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "len" objects de taille 8bits à partir du résultat de longueur len*2
        REGINDEX regIndex = getRegIndex(regSrcDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_2RR

template<UINT32 len> 
void BINARY::sIMUL_3M(THREADID tid, ADDRINT value, ADDRINT readAddress, REG regDest ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if (!pTmgrGlobal->isMemoryTainted<len>(readAddress)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();    
        pTmgrTls->unTaintRegister<len>(regDest);
    }			
    else 
    {
        _LOGTAINT("imul3IM" << len << " ");

        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*len)>> resultPtr = std::make_shared<TaintObject<(2*len)>>(
            X_IMUL,
            ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress)),
            ObjectSource(len, value));

        // marquage des flags
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "len" objects de taille 8bits à partir du résultat de longueur len*2
        REGINDEX regIndex = getRegIndex(regDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {
            pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                EXTRACT,
                objResult,
                ObjectSource(8, regPart)));
        }
    }
} // sIMUL_3M

template<UINT32 len> 
void BINARY::sIMUL_3R(THREADID tid, ADDRINT value, REG regSrc, ADDRINT regSrcValue, REG regDest ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if (!pTmgrTls->isRegisterTainted<len>(regSrc)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
        pTmgrTls->unTaintRegister<len>(regDest);
    }			
    else 
    {
        _LOGTAINT("imul3IR" << len << " ");

        // longueur résultat = double des sources	
        std::shared_ptr<TaintObject<(2*len)>> resultPtr = std::make_shared<TaintObject<(2*len)>>(
            X_IMUL,
            ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue)),
            ObjectSource(len, value));

        // marquage des flags (uniquement besoin du résultat) 
        fTaintIMUL(pTmgrTls, resultPtr);	
        
        // marquage de la destination avec partie basse du résultat (partie haute ignorée)
        // => marquage de "len" objects de taille 8bits à partir du résultat de longueur len*2
        REGINDEX regIndex = getRegIndex(regDest);
        ObjectSource objResult(resultPtr);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
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
 template<UINT32 len> void BINARY::sDIVISION_M(THREADID tid, ADDRINT readAddress, 
    bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG)
{
    // dividende = registre (len*2 bits, composé), diviseur = mémoire (len bits)
    // partie faible du dividende = registre d'accumulation (AL/AX/EAX/RAX)
    // partie forte du dividende = registre d'I/O (AH/DX/EDX/RDX)
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<len>::getReg(); 
    REG regIO  = registerIO<len>::getReg();  
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isDivisorTainted =      pTmgrGlobal->isMemoryTainted<len>(readAddress);
    bool isLowDividendTainted  = pTmgrTls->isRegisterTainted<len>(regACC);
    bool isHighDividendTainted = pTmgrTls->isRegisterTainted<len>(regIO);
    
    if (isLowDividendTainted || isHighDividendTainted || isDivisorTainted) 
    {
        _LOGTAINT(((isSignedDivision) ? "I" : "") << "DIVM " << len << " " );

        ObjectSource objSrcLowDividend = (isLowDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regACC, lowDividendValue))
            : ObjectSource(len, lowDividendValue);

        ObjectSource objSrcHighDividend = (isHighDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regIO, highDividendValue))
            : ObjectSource(len, highDividendValue);
  
        ObjectSource objSrcDivisor = (isDivisorTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, getMemoryValue<len>(readAddress));

        // création de l'objet correspondant au quotient
        TaintObject<len> quotient(
            (isSignedDivision) ? X_IDIV_QUO : X_DIV_QUO, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);
        
        // création de l'objet correspondant au reste
        TaintObject<len> remainder(
            (isSignedDivision) ? X_IDIV_REM : X_DIV_REM, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);

        // Affectation quotient et reste aux registres adéquats (idem dividende, cf manuel Intel)
        pTmgrTls->updateTaintRegister<len>(regACC, std::make_shared<TaintObject<len>>(quotient));
        pTmgrTls->updateTaintRegister<len>(regIO,  std::make_shared<TaintObject<len>>(remainder));	
    }
} // sDIVISION_M

template<UINT32 len> void BINARY::sDIVISION_R(THREADID tid, REG regSrc, ADDRINT regSrcValue, 
    bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG)
{
    // dividende = registre (len*2 bits, composé), diviseur = mémoire (len bits)
    // partie faible du dividende = registre d'accumulation (AL/AX/EAX/RAX)
    // partie forte du dividende = registre d'I/O (AH/DX/EDX/RDX)
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<len>::getReg(); 
    REG regIO  = registerIO<len>::getReg();  
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    bool isDivisorTainted      = pTmgrTls->isRegisterTainted<len>(regSrc, regSrcValue);
    bool isLowDividendTainted  = pTmgrTls->isRegisterTainted<len>(regACC);
    bool isHighDividendTainted = pTmgrTls->isRegisterTainted<len>(regIO);
    
    if (isLowDividendTainted || isLowDividendTainted || isDivisorTainted) 
    {
        _LOGTAINT(((isSignedDivision) ? "I" : "") << "DIVR " << len << " " );

        ObjectSource objSrcLowDividend = (isLowDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regACC, lowDividendValue))
            : ObjectSource(len, lowDividendValue);

        ObjectSource objSrcHighDividend = (isHighDividendTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regIO, highDividendValue))
            : ObjectSource(len, highDividendValue);

        ObjectSource objSrcDivisor = (isDivisorTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
         
        // création de l'objet correspondant au quotient
        TaintObject<len> quotient(
            (isSignedDivision) ? X_IDIV_QUO : X_DIV_QUO, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);
        
        // création de l'objet correspondant au reste
        TaintObject<len> remainder(
            (isSignedDivision) ? X_IDIV_REM : X_DIV_REM, /* division signée ou non */
            objSrcLowDividend,
            objSrcHighDividend,
            objSrcDivisor);

        // Affectation quotient et reste aux registres adéquats (idem dividende, cf manuel Intel)
        pTmgrTls->updateTaintRegister<len>(regACC, std::make_shared<TaintObject<len>>(quotient));
        pTmgrTls->updateTaintRegister<len>(regIO,  std::make_shared<TaintObject<len>>(remainder));	
    }
} //sDIVISION_R