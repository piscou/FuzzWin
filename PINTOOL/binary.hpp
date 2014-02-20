/////////
// NEG //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sNEG_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))  pTmgrTls->unTaintAllFlags(); 
    else 
    {
        _LOGTAINT("negM" << lengthInBits);
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));

        // création de l'objet résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_NEG, objSrc);

        // marquage flags et destination
        fTaintNEG(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sNEG_M

template<UINT32 lengthInBits> 
void BINARY::sNEG_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("negR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));

        // création de l'objet résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_NEG, objSrc);

        // marquage flags et destination
        fTaintNEG(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sNEG_R

/////////
// INC //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sINC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("incM");
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        
        // création de l'objet résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_INC, objSrc);

        // marquage flags et destination
        fTaintINC(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sINC_M

template<UINT32 lengthInBits> 
void BINARY::sINC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg)) fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("incR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        
        // création de l'objet résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_INC, objSrc);

        // marquage flags et destination
        fTaintINC(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sINC_R

/////////
// DEC //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sDEC_M(THREADID tid, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))  fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("decM");
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));

        // création de l'objet résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_DEC, objSrc);

        // marquage flags et destination
        fTaintDEC(pTmgrTls, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sDEC_M

template<UINT32 lengthInBits> 
void BINARY::sDEC_R(THREADID tid, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg))  fUnTaintINCDEC(pTmgrTls);
    else 
    {
        _LOGTAINT("decR");
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        
        // création de l'objet résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_DEC, objSrc);

        // marquage flags et destination
        fTaintDEC(pTmgrTls, objSrc, resultPtr);
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sDEC_R

/////////
// ADC //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sADC_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue, 
                     ADDRINT flagsValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCFTainted  = pTmgrTls->isCarryFlagTainted();
    bool isRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(reg);

    // rien de marqué : juste un démarquage des flags
    if (! (isCFTainted || isRegTainted))    pTmgrTls->unTaintAllFlags();  
    else
    {
        _LOGTAINT("ADC_IR " << lengthInBits);

        // On va calculer deux sources : 'objSrcPlusDest' et 'objCarryFlag'
        // puis les additionner et marquer flags et destination

        // objets sources à calculer
        ObjectSource objSrcPlusDest, objCarryFlag;
        
        /*** traitement de 'objSrcPlusDest' : 2 cas possibles selon marquage reg ***/
        if (isRegTainted)  
        {  
            objSrcPlusDest = ObjectSource(MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue)),
                ObjectSource(lengthInBits, value)));
        }
        else objSrcPlusDest = ObjectSource(lengthInBits, value + regValue);

        /*** traitement de 'objCarryFlag' : 2 cas possibles (marqué ou valeur) ***/
        if (isCFTainted)	
        {
            // CF doit être zero-extended à la longueur des sources
            TAINT_OBJECT_PTR zeroExtCFPtr = MK_TAINT_OBJECT_PTR(X_ZEROEXTEND,
                ObjectSource(pTmgrTls->getTaintCarryFlag()));
            objCarryFlag = ObjectSource(zeroExtCFPtr);
        }
        else objCarryFlag = ObjectSource(lengthInBits, flagsValue & 1); // CF est le LSB des flags

        /*** resultat = addition des deux sources ***/
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcPlusDest, objCarryFlag);

        /*** marquage flags et destination ***/
        fTaintADD(pTmgrTls, objSrcPlusDest, objCarryFlag, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);			
    }  
} // sADC_IR

template<UINT32 lengthInBits> 
void BINARY::sADC_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress, 
                     ADDRINT flagsValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // Cas où CF est marqué : addition CF et (mem + Imm)
    if (pTmgrTls->isCarryFlagTainted())	
    {
        // CF doit être zero-extended à la longueur des sources
        ObjectSource objCF(MK_TAINT_OBJECT_PTR(
            X_ZEROEXTEND,
            ObjectSource(pTmgrTls->getTaintCarryFlag())));

        // construction du squelette du resultat : CF + ...
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objCF);

        // ajout de (mem + Imm), selon marquage de la mémoire
        ObjectSource objMemImm;
        if (pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) 
        {
            _LOGTAINT("ADC_IM " << lengthInBits << "(MEM et CF marqués)");
            TAINT_OBJECT_PTR tMemImmPtr = MK_TAINT_OBJECT_PTR(X_ADD,
                ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)),
                ObjectSource(lengthInBits, value));
            objMemImm = ObjectSource(tMemImmPtr);
        }
        else
        {
            _LOGTAINT("ADC_IM " << lengthInBits << "(CF marqué mais pas MEM)");
            ADDRINT memValue = getMemoryValue<lengthInBits>(writeAddress);
            objMemImm = ObjectSource(lengthInBits, memValue + value);
        }
        resultPtr->addSource(objMemImm);
        
        // marquage flags et destination. Les deux sources sont CF et (mem+imm)
        fTaintADD(pTmgrTls, objCF, objMemImm, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }  
    // cas où mémoire marquée (CF non marqué)
    else if (pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))
    {
        _LOGTAINT("ADC_IM " << lengthInBits << "(MEM marquée, pas CF)");

        // addition mem + (imm + valeur CF)
        ObjectSource objMem(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        ObjectSource objImmCF(lengthInBits, value + (flagsValue & 1));		
        
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objMem, objImmCF);

        // marquage flags et destination. Les deux sources sont mem et (imm + CF)
        fTaintADD(pTmgrTls, objMem, objImmCF, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
    // ni MEM ni CF marqué : juste un démarquage des flags
    else pTmgrTls->unTaintAllFlags();  
} // sADC_IM

template<UINT32 lengthInBits> 
void BINARY::sADC_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, 
                     ADDRINT regSrcDestValue, ADDRINT flagsValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCFTainted  = pTmgrTls->isCarryFlagTainted();
    bool isRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    bool isMemTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress);
    
    // rien de marqué : juste un démarquage des flags
    if (! (isCFTainted || isRegTainted || isMemTainted))
    {
        pTmgrTls->unTaintAllFlags();  
    }
    else
    {
        _LOGTAINT("ADC_MR " << lengthInBits);

        // On va calculer deux sources : 'objSrcPlusDest' et 'objCarryFlag'
        // puis les additionner et marquer flags et destination

        // objets sources à calculer
        ObjectSource objSrcPlusDest, objCarryFlag;
        
        /*** traitement de 'objSrcPlusDest' : 4 cas possibles (M/M, M/V, V/M, V/V) ***/
        if (isRegTainted)  
        {  
            TAINT_OBJECT_PTR tMemRegPtr = MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue)));
            
            if (isMemTainted) // Cas M/M
            {  
                tMemRegPtr->addSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress));
            }
            else // cas M/V
            {
                ADDRINT memValue = getMemoryValue<lengthInBits>(readAddress);
                tMemRegPtr->addConstantAsASource<lengthInBits>(memValue);
            }
            // résultat reg + mem traduit sous forme de source
            objSrcPlusDest = ObjectSource(tMemRegPtr);
        }
        else if (isMemTainted) // cas V/M
        {
            objSrcPlusDest = ObjectSource(MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress)),
                ObjectSource(lengthInBits, regSrcDestValue)));
        }
        else // cas V/V
        {
            ADDRINT memValue = getMemoryValue<lengthInBits>(readAddress);
            objSrcPlusDest = ObjectSource(lengthInBits, memValue + regSrcDestValue);
        }

        /*** traitement de 'objCarryFlag' : 2 cas possibles (marqué ou valeur) ***/
        if (isCFTainted)	
        {
            // CF doit être zero-extended à la longueur des sources
            TAINT_OBJECT_PTR zeroExtCFPtr = MK_TAINT_OBJECT_PTR(X_ZEROEXTEND,
                ObjectSource(pTmgrTls->getTaintCarryFlag()));
            objCarryFlag = ObjectSource(zeroExtCFPtr);
        }
        else objCarryFlag = ObjectSource(lengthInBits, flagsValue & 1); // CF est le LSB des flags

        /*** resultat = addition des deux sources ***/
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcPlusDest, objCarryFlag);

        /*** marquage flags et destination ***/
        fTaintADD(pTmgrTls, objSrcPlusDest, objCarryFlag, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }  
} // sADC_MR

template<UINT32 lengthInBits> 
void BINARY::sADC_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress, 
                     ADDRINT flagsValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCFTainted  = pTmgrTls->isCarryFlagTainted();
    bool isRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);
    bool isMemTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);  

    // rien de marqué : juste un démarquage des flags
    if (! (isCFTainted || isRegTainted || isMemTainted))
    {
        pTmgrTls->unTaintAllFlags();  
    }
    else
    {
        _LOGTAINT("ADC_RM " << lengthInBits);

        // On va calculer deux sources : 'objSrcPlusDest' et 'objCarryFlag'
        // puis les additionner et marquer flags et destination

        // objets sources à calculer
        ObjectSource objSrcPlusDest, objCarryFlag;
        
        /*** traitement de 'objSrcPlusDest' : 4 cas possibles (M/M, M/V, V/M, V/V) ***/
        if (isRegTainted)  
        {  
            TAINT_OBJECT_PTR tMemRegPtr = MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue)));
            
            if (isMemTainted) // Cas M/M
            {  
                tMemRegPtr->addSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
            }
            else // cas M/V
            {
                ADDRINT memValue = getMemoryValue<lengthInBits>(writeAddress);
                tMemRegPtr->addConstantAsASource<lengthInBits>(memValue);
            }
            // résultat reg + mem traduit sous forme de source
            objSrcPlusDest = ObjectSource(tMemRegPtr);
        }
        else if (isMemTainted) // cas V/M
        {
            objSrcPlusDest = ObjectSource(MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)),
                ObjectSource(lengthInBits, regSrcValue)));
        }
        else // cas V/V
        {
            ADDRINT memValue = getMemoryValue<lengthInBits>(writeAddress);
            objSrcPlusDest = ObjectSource(lengthInBits, memValue + regSrcValue);
        }

        /*** traitement de 'objCarryFlag' : 2 cas possibles (marqué ou valeur) ***/
        if (isCFTainted)	
        {
            // CF doit être zero-extended à la longueur des sources
            TAINT_OBJECT_PTR zeroExtCFPtr = MK_TAINT_OBJECT_PTR(X_ZEROEXTEND,
                ObjectSource(pTmgrTls->getTaintCarryFlag()));
            objCarryFlag = ObjectSource(zeroExtCFPtr);
        }
        else objCarryFlag = ObjectSource(lengthInBits, flagsValue & 1); // CF est le LSB des flags

        /*** resultat = addition des deux sources ***/
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcPlusDest, objCarryFlag);

        /*** marquage flags et destination ***/
        fTaintADD(pTmgrTls, objSrcPlusDest, objCarryFlag, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }  
} // sADC_RM

template<UINT32 lengthInBits> 
void BINARY::sADC_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, 
                     ADDRINT regSrcDestValue, ADDRINT flagsValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCFTainted          = pTmgrTls->isCarryFlagTainted();
    bool isRegSrcTainted      = pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);
    bool isRegSrcDestTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(regSrcDest);
    
    // rien de marqué : juste un démarquage des flags
    if (! (isCFTainted || isRegSrcTainted || isRegSrcDestTainted))
    {
        pTmgrTls->unTaintAllFlags();  
    }
    else
    {
        _LOGTAINT("ADC_RR " << lengthInBits);

        // On va calculer deux sources : 'objSrcPlusDest' et 'objCarryFlag'
        // puis les additionner et marquer flags et destination

        // objets sources à calculer
        ObjectSource objSrcPlusDest, objCarryFlag;
        
        /*** traitement de 'objSrcPlusDest' : 4 cas possibles (M/M, M/V, V/M, V/V) ***/
        if (isRegSrcTainted)  
        {  
            TAINT_OBJECT_PTR tRegRegPtr = MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue)));
            
            if (isRegSrcDestTainted) // Cas M/M
            {  
                tRegRegPtr->addSource(
                    pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue));
            }
            // cas M/V
            else  tRegRegPtr->addConstantAsASource<lengthInBits>(regSrcDestValue);
            // résultat reg + mem traduit sous forme de source
            objSrcPlusDest = ObjectSource(tRegRegPtr);
        }
        else if (isRegSrcDestTainted) // cas V/M
        {
            objSrcPlusDest = ObjectSource(MK_TAINT_OBJECT_PTR(X_ADD, 
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrcDest, regSrcDestValue)),
                ObjectSource(lengthInBits, regSrcValue)));
        }
        // cas V/V
        else objSrcPlusDest = ObjectSource(lengthInBits, regSrcDestValue + regSrcValue);

        /*** traitement de 'objCarryFlag' : 2 cas possibles (marqué ou valeur) ***/
        if (isCFTainted)	
        {
            // CF doit être zero-extended à la longueur des sources
            TAINT_OBJECT_PTR zeroExtCFPtr = MK_TAINT_OBJECT_PTR(X_ZEROEXTEND,
                ObjectSource(pTmgrTls->getTaintCarryFlag()));
            objCarryFlag = ObjectSource(zeroExtCFPtr);
        }
        else objCarryFlag = ObjectSource(lengthInBits, flagsValue & 1); // CF est le LSB des flags

        /*** resultat = addition des deux sources ***/
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcPlusDest, objCarryFlag);

        /*** marquage flags et destination ***/
        fTaintADD(pTmgrTls, objSrcPlusDest, objCarryFlag, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }  
} // sADC_RR


/////////
// ADD //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sADD_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addIR" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        ObjectSource objSrc(lengthInBits, value);		
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);			
    }
} // sADD_IR

template<UINT32 lengthInBits> 
void BINARY::sADD_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("addIM" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        ObjectSource objSrc(lengthInBits, value);		
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sADD_IM

template<UINT32 lengthInBits> 
void BINARY::sADD_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // marquage flags et dest
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }
} // sADD_MR

template<UINT32 lengthInBits> 
void BINARY::sADD_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sADD_RM

template<UINT32 lengthInBits> 
void BINARY::sADD_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objSrcDest, objSrc);

        // marquage flags et destination
        fTaintADD(pTmgrTls, objSrcDest, objSrc, resultPtr);   
        pTmgrTls->updateTaintRegister<lengthInBits>(regSrcDest, resultPtr);			
    }
} // sADD_RR

/////////
// ADC //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sSBB_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue, ADDRINT flagsValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // Cas où CF est marqué : addition CF et (reg + Imm)
    if (pTmgrTls->isCarryFlagTainted())	
    {
        // CF doit être zero-extended à la longueur des sources
        ObjectSource objCF(MK_TAINT_OBJECT_PTR( X_ZEROEXTEND,
            ObjectSource(pTmgrTls->getTaintCarryFlag())));

        // construction du squelette du resultat : CF + ...
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objCF);

        // ajout de (reg + Imm), selon marquage de reg
        ObjectSource objRegImm;
        if (pTmgrTls->isRegisterTainted<lengthInBits>(reg)) 
        {
            _LOGTAINT("SBBIR " << lengthInBits << "(REG et CF marqués)");
            TAINT_OBJECT_PTR tRegImmPtr = MK_TAINT_OBJECT_PTR(X_ADD,
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue)),
                ObjectSource(lengthInBits, value));
            objRegImm = ObjectSource(tRegImmPtr);
        }
        else
        {
            _LOGTAINT("SBBIR " << lengthInBits << "(CF marqué mais pas REG)");
            objRegImm = ObjectSource(lengthInBits, regValue + value);
        }
        resultPtr->addSource(objRegImm);
        
        // marquage flags et destination. Les deux sources sont CF et (reg+imm)
        fTaintADD(pTmgrTls, objCF, objRegImm, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);			
    }  
    // cas où registre marqué (CF non marqué)
    else if (pTmgrTls->isRegisterTainted<lengthInBits>(reg))
    {
        _LOGTAINT("SBBIR " << lengthInBits << "(REG marqué, pas CF)");

        // addition reg + (imm + valeur CF)
        ObjectSource objReg(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        ObjectSource objImmCF(lengthInBits, value + (flagsValue & 1));		
        
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objReg, objImmCF);

        // marquage flags et destination. Les deux sources sont reg et (imm + CF)
        fTaintADD(pTmgrTls, objReg, objImmCF, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
    // ni REG ni CF marqué : juste un démarquage des flags
    else pTmgrTls->unTaintAllFlags(); 
} // sSBB_IR

template<UINT32 lengthInBits> 
void BINARY::sSBB_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress, 
                     ADDRINT flagsValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // Cas où CF est marqué : addition CF et (mem + Imm)
    if (pTmgrTls->isCarryFlagTainted())	
    {
        // CF doit être zero-extended à la longueur des sources
        ObjectSource objCF(MK_TAINT_OBJECT_PTR(
            X_ZEROEXTEND,
            ObjectSource(pTmgrTls->getTaintCarryFlag())));

        // construction du squelette du resultat : CF + ...
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objCF);

        // ajout de (mem + Imm), selon marquage de la mémoire
        ObjectSource objMemImm;
        if (pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) 
        {
            _LOGTAINT("SBBIM " << lengthInBits << "(MEM et CF marqués)");
            TAINT_OBJECT_PTR tMemImmPtr = MK_TAINT_OBJECT_PTR(X_ADD,
                ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)),
                ObjectSource(lengthInBits, value));
            objMemImm = ObjectSource(tMemImmPtr);
        }
        else
        {
            _LOGTAINT("SBBIM " << lengthInBits << "(CF marqué mais pas MEM)");
            ADDRINT memValue = getMemoryValue<lengthInBits>(writeAddress);
            objMemImm = ObjectSource(lengthInBits, memValue + value);
        }
        resultPtr->addSource(objMemImm);
        
        // marquage flags et destination. Les deux sources sont CF et (mem+imm)
        fTaintADD(pTmgrTls, objCF, objMemImm, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }  
    // cas où mémoire marquée (CF non marqué)
    else if (pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))
    {
        _LOGTAINT("SBBIM " << lengthInBits << "(MEM marquée, pas CF)");

        // addition mem + (imm + valeur CF)
        ObjectSource objMem(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        ObjectSource objImmCF(lengthInBits, value + (flagsValue & 1));		
        
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_ADD, objMem, objImmCF);

        // marquage flags et destination. Les deux sources sont mem et (imm + CF)
        fTaintADD(pTmgrTls, objMem, objImmCF, resultPtr);	
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
    // ni MEM ni CF marqué : juste un démarquage des flags
    else pTmgrTls->unTaintAllFlags();  
} // sSBB_IM

template<UINT32 lengthInBits> 
void BINARY::sSBB_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, 
                     ADDRINT regSrcDestValue, ADDRINT flagsValue ADDRESS_DEBUG) 
{
} // sSBB_MR

template<UINT32 lengthInBits> 
void BINARY::sSBB_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress, ADDRINT flagsValue ADDRESS_DEBUG)
{
} // sSBB_RM

template<UINT32 lengthInBits> 
void BINARY::sSBB_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue, ADDRINT flagsValue ADDRESS_DEBUG) 
{
} // sSBB_RR



/////////
// SUB //
/////////

// SIMULATE
template<UINT32 lengthInBits> 
void BINARY::sSUB_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subIR" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue));
        ObjectSource objSrc(lengthInBits, value);		
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);	
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);			
    }
} // sSUB_IR

template<UINT32 lengthInBits> 
void BINARY::sSUB_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("subIM" << lengthInBits << " ");

        ObjectSource objSrcDest(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress));
        ObjectSource objSrc(lengthInBits, value);		
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
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
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
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
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_SUB,
            objSrcDest,
            objSrc);

        // marquage flags et destination
        fTaintSUB(pTmgrTls, objSrcDest, objSrc, resultPtr);
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);			
    }
} // sSUB_RM

template<UINT32 lengthInBits> 
void BINARY::sSUB_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
    
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
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
template<UINT32 lengthInBits> 
void BINARY::sCMP_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg) )	pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpIR" << lengthInBits << " ");

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue)), ObjectSource(lengthInBits, value));			
    }
} // sCMP_IR

template<UINT32 lengthInBits> 
void BINARY::sCMP_IM(THREADID tid, ADDRINT value, ADDRINT readAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpIM" << lengthInBits << " ");

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress)), ObjectSource(lengthInBits, value));					
    }
} // sCMP_IM

template<UINT32 lengthInBits> 
void BINARY::sCMP_MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
void BINARY::sCMP_RM(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT readAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress); 
    bool isSrcTainted =		pTmgrTls->isRegisterTainted<lengthInBits>(regSrc);

    if ( !(isSrcDestTainted || isSrcTainted))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("cmpRM" << lengthInBits << " ");
           	
        ObjectSource objSrcDest = (isSrcDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(readAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(readAddress));

        ObjectSource objSrc = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(regSrc, regSrcValue))
            : ObjectSource(lengthInBits, regSrcValue);

        // marquage flags
        fTaintCMP<lengthInBits>(pTmgrTls, objSrcDest, objSrc);	
    }
} // sCMP_RM

template<UINT32 lengthInBits> 
void BINARY::sCMP_RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
template<UINT32 lengthInBits> 
void BINARY::fTaintCMP(TaintManager_Thread *pTmgrTls, const ObjectSource &objSrcDest, const ObjectSource &objSrc) 
{
    ObjectSource objResult(MK_TAINT_OBJECT_PTR(
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
template<UINT32 lengthInBits> 
void BINARY::sIMUL_1M(THREADID tid, ADDRINT readAddress, ADDRINT implicitRegValue ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

template<UINT32 lengthInBits> 
void BINARY::sIMUL_1R(THREADID tid, REG regSrc, ADDRINT regSrcValue, ADDRINT implicitRegValue ADDRESS_DEBUG) 
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

template<UINT32 lengthInBits> 
void BINARY::sIMUL_2MR(THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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

template<UINT32 lengthInBits> 
void BINARY::sIMUL_2RR(THREADID tid, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
 template<UINT32 lengthInBits> 
 void BINARY::sDIVISION_M(THREADID tid, ADDRINT readAddress,
    bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG)
{
    // dividende = registre (lengthInBits*2 bits, composé), diviseur = mémoire (lengthInBits bits)
    // partie faible du dividende = registre d'accumulation (AL/AX/EAX/RAX)
    // partie forte du dividende = registre d'I/O (AH/DX/EDX/RDX)
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<lengthInBits>::getReg(); 
    REG regIO  = registerIO<lengthInBits>::getReg();  
    
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
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
        pTmgrTls->updateTaintRegister<lengthInBits>(regACC, MK_TAINT_OBJECT_PTR(quotient));
        pTmgrTls->updateTaintRegister<lengthInBits>(regIO,  MK_TAINT_OBJECT_PTR(remainder));	
    }
} // sDIVISION_M

template<UINT32 lengthInBits> 
void BINARY::sDIVISION_R(THREADID tid, REG regSrc, ADDRINT regSrcValue, 
    bool isSignedDivision, ADDRINT lowDividendValue, ADDRINT highDividendValue ADDRESS_DEBUG)
{
    // dividende = registre (lengthInBits*2 bits, composé), diviseur = mémoire (lengthInBits bits)
    // partie faible du dividende = registre d'accumulation (AL/AX/EAX/RAX)
    // partie forte du dividende = registre d'I/O (AH/DX/EDX/RDX)
    // valeurs fixes calculées à la compilation (métaprogrammation)
    REG regACC = registerACC<lengthInBits>::getReg(); 
    REG regIO  = registerIO<lengthInBits>::getReg();  
    
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isDivisorTainted      = pTmgrTls->isRegisterTainted<lengthInBits>(regSrc, regSrcValue);
    bool isLowDividendTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(regACC);
    bool isHighDividendTainted = pTmgrTls->isRegisterTainted<lengthInBits>(regIO);
    
    if (isLowDividendTainted || isHighDividendTainted || isDivisorTainted) 
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
        pTmgrTls->updateTaintRegister<lengthInBits>(regACC, MK_TAINT_OBJECT_PTR(quotient));
        pTmgrTls->updateTaintRegister<lengthInBits>(regIO,  MK_TAINT_OBJECT_PTR(remainder));	
    }
} //sDIVISION_R