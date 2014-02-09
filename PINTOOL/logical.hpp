
///////////////
///// AND /////
///////////////

// SIMULATE
template<UINT32 len> void LOGICAL::sAND_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrGlobal->isMemoryTainted<len>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else if (!value) // AND x, 0 = 0, donc démarquage destination et flags
    { 
        pTmgrTls->unTaintAllFlags();
        pTmgrGlobal->unTaintMemory<len>(writeAddress);
    }
    else 
    {
        _LOGTAINT("andIM" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)),
            ObjectSource(len, value)));

        // MARQUAGE DE LA DESTINATION, par octet pour éviter surmarquage
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++writeAddress)
        {
            // dest non marquée : ne rien faire
            if (!pTmgrGlobal->isMemoryTainted<8>(writeAddress)) continue;
        
            UINT32 value8bits = EXTRACTBYTE(value, byteNbr);

            // 1er cas : valeur = 0xff : aucun changement
            if (value8bits == 0xff) continue;      
            // 2eme cas : valeur nulle  => démarquage (AND x, 0 = tjs 0)
            else if (!value8bits) pTmgrGlobal->unTaintMemory<8>(writeAddress);
            // sinon, marquage du résultat avec opération "AND"
            else 
            {
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                    ObjectSource(8, value8bits)));
            }
        }   
    }
} // sAND_IM

template<UINT32 len> void LOGICAL::sAND_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags();
    else if (!value)  // AND x, 0 = 0, donc démarquage destination et flags
    {
        pTmgrTls->unTaintAllFlags();
        pTmgrTls->unTaintRegister<len>(reg);
    }
    else 
    {
        _LOGTAINT("andIR" << len);

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue)),
            ObjectSource(len, value)));

        // MARQUAGE DE LA DESTINATION
        REGINDEX regIndex = getRegIndex(reg);
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {
            // dest non marquée : ne rien faire
            if (!pTmgrTls->isRegisterPartTainted(regIndex, regPart)) continue;
        
            UINT32 value8bits = EXTRACTBYTE(value, regPart);

            // 1er cas : valeur = 0xff :  aucun changement
            if (value8bits == 0xff) continue;  

            // 2eme cas : valeur nulle  => démarquage (AND x, 0 = tjs 0)
            else if (!value8bits) pTmgrTls->unTaintRegisterPart(regIndex, regPart);

            // sinon, marquage du résultat avec opération "AND"
            else 
            { 
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart)),  
                    ObjectSource(8, value8bits)));
            }
        }
    }
} // sAND_IR

template<UINT32 len> void LOGICAL::sAND_RM
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT destValue = getMemoryValue<len>(writeAddress);

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    // cas particuliers du AND (cf tableau)
    //if (!isDestTainted && (!isSrcTainted || !destValue)) pTmgr->unTaintAllFlags(); => 5 opérations
    if (!(isDestTainted || (isSrcTainted && (destValue != 0)))) pTmgrTls->unTaintAllFlags(); // 3 opérations
    else if ( !(isSrcTainted || (srcValue != 0))) 
    {
        pTmgrTls->unTaintAllFlags();
        if (isDestTainted) pTmgrGlobal->unTaintMemory<len>(writeAddress);
    }
    else 
    { 
        // dans tous les autres cas, marquage d'abord des flags puis de la destination octet par octet
        _LOGTAINT("andRM" << len);

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)) 
            : ObjectSource(len, destValue);

        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION, octet par octet
        // plusieurs cas selon le marquage des opérandes, cf tableau AND
        
        REGINDEX regSrcIndex = getRegIndex(regSrc);
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++writeAddress) 
        {   
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, byteNbr);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, byteNbr);
            bool isSrc8bitsTainted  = pTmgrTls->isRegisterPartTainted(regSrcIndex, byteNbr);
            bool isDest8bitsTainted = pTmgrGlobal->isMemoryTainted<8>(writeAddress);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;

            // CAS 2 : destination non marquée (et donc source marquée, sinon cas 1)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : dest = 0 ; (AND 0, src = 0), donc continuer (dest déjà démarquée)
                if (!dest8bitsValue) continue;
                // cas 2.2 : destination vaut 0xff ; (AND 0xff, src) équivaut à MOV dest, src
                else if (dest8bitsValue == 0xff)
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr))));
                }
                // cas 2.3 : autres valeur de la destination => marquage via AND
                else 
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_AND,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr)),
                        ObjectSource(8, dest8bitsValue)));            
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0 ; (AND dest, 0) fera tjs 0, donc démarquer destination
                if (!src8bitsValue) pTmgrGlobal->unTaintMemory<8>(writeAddress);
                // cas 3.2 : src vaut 0xff; (AND dest, 0xff) ne modifie pas dest => continuer
                else if (src8bitsValue == 0xff) continue;
                // cas 3.3 : autres valeurs de la source => marquage via AND
                else 
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_AND,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                        ObjectSource(8, src8bitsValue)));    
                }
            }
            // CAS 4 : source et destination marquées => marquage via AND
            else 
            {
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr)))); 
            }
        }   
    }
} //sAND_RM

template<UINT32 len> void LOGICAL::sAND_MR
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT srcValue = getMemoryValue<len>(readAddress);

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted  = pTmgrGlobal->isMemoryTainted<len>(readAddress);
    
    // cas particuliers du AND (cf tableau)
    // if (!isDestTainted && (!isSrcTainted || !destValue)) pTmgr->unTaintAllFlags(); => 5 opérations
    if (!(isDestTainted || (isSrcTainted && (destValue != 0)))) pTmgrTls->unTaintAllFlags(); // 3 opérations
    else if ( !(isSrcTainted || (srcValue != 0))) 
    {
        pTmgrTls->unTaintAllFlags();
        if (isDestTainted) pTmgrTls->unTaintRegister<len>(regSrcDest);
    }
    else 
    { 
        // sinon, marquage d'abord des flags puis de la destination octet par octet
        _LOGTAINT("andMR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION, octet par octet
        // plusieurs cas selon le marquage des opérandes, cf tableau AND
        
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++readAddress) 
        {   
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, byteNbr);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, byteNbr);
            bool isSrc8bitsTainted  = pTmgrGlobal->isMemoryTainted<8>(readAddress);
            bool isDest8bitsTainted = pTmgrTls->isRegisterPartTainted(regSrcDestIndex, byteNbr);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;  

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : dest = 0 ; (AND 0, src) fera tjs 0 => continuer (dest déjà démarquée)
                if (!dest8bitsValue) continue;
                // cas 2.2 : destination vaut 0xff ; (AND 0xff, src) équivaut à MOV dest, src
                else if (dest8bitsValue == 0xff)  
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
                }
                // cas 2.3 : autres valeur de la destination => marquage via AND
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_AND,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),
                        ObjectSource(8, dest8bitsValue)));
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0 ; (AND dest, 0) fera tjs 0, donc démarquer destination
                if (!src8bitsValue) pTmgrTls->unTaintRegisterPart(regSrcDestIndex, byteNbr);
                // cas 3.2 : src vaut 0xff ; (AND dest, 0xff) ne modifie pas dest => continuer
                else if (src8bitsValue == 0xff) continue;               
                // cas 3.3 : autres valeur de la source => marquage via AND
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_AND,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr)),
                        ObjectSource(8, src8bitsValue)));        
                }                                   
            }
            // CAS 4 : source et destination marquées => marquage via AND
            else 
            {
                pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr)),
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));        
            }   
        }
    }
} // sAND_MR

template<UINT32 len> void LOGICAL::sAND_RR
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    // cas particuliers du AND (cf tableau)
    //if (!maskDest && (!maskSrc || !destValue)) pTmgr->unTaintAllFlags(); => 5 opérations
    if (!(isDestTainted || (isSrcTainted && (destValue != 0)))) pTmgrTls->unTaintAllFlags(); // 3 opérations
    else if ( !(isSrcTainted || (srcValue != 0))) 
    {
        pTmgrTls->unTaintAllFlags();
        if (isDestTainted) pTmgrTls->unTaintRegister<len>(regSrcDest);
    }
    else 
    {
        _LOGTAINT("andRR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION
        // plusieurs cas selon le marquage des opérandes, cf tableau AND
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        REGINDEX regSrcIndex     = getRegIndex(regSrc);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {  
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, regPart);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, regPart);
            bool isSrc8bitsTainted  = pTmgrTls->isRegisterPartTainted(regSrcIndex, regPart);
            bool isDest8bitsTainted = pTmgrTls->isRegisterPartTainted(regSrcDestIndex, regPart);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : dest = 0 ; (AND 0, src) = tjs 0, donc continuer (dest déjà démarquée)
                if (!dest8bitsValue) continue;
                // cas 2.2 : destination vaut 0xff ; (AND 0xff, src) équivaut à MOV dest, src
                else if (dest8bitsValue == 0xff) 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart))));
                }
                // cas 2.3 : autres valeur de la destination => marquage via AND
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_AND,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart)),
                        ObjectSource(8, dest8bitsValue)));
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0 ; (AND dest, 0) fera tjs 0, donc démarquer destination
                if (!src8bitsValue) pTmgrTls->unTaintRegisterPart(regSrcDestIndex, regPart);
                // cas 3.2 : src vaut 0xff ; (AND dest, 0xff) ne modifie pas dest => continuer
                else if (src8bitsValue == 0xff) continue;
                // cas 3.3 : autres valeur de la source => marquage via AND
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_AND,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart)),
                        ObjectSource(8, src8bitsValue)));  
                }                                   
            }
            // CAS 4 : source et destination marquées => marquage via AND
            else 
            {
                pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                    X_AND,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart)),
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart))));
            }   
        }
    }
} // sAND_RR

//////////////
///// OR /////
//////////////

// SIMULATE
template<UINT32 len> void LOGICAL::sOR_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrGlobal->isMemoryTainted<len>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else if (value == minusOne<len>::get()) 
    { 
        // OR x, 0xff... = 0xff..., donc démarquage destination et flags
        pTmgrTls->unTaintAllFlags();
        pTmgrGlobal->unTaintMemory<len>(writeAddress);
    }
    else 
    {
        _LOGTAINT("orIM" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_OR,
            ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)),
            ObjectSource(len, value)));

        // MARQUAGE DE LA DESTINATION, par octet pour éviter surmarquage
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++writeAddress)
        {
            // dest non marquée : ne rien faire
            if (!pTmgrGlobal->isMemoryTainted<8>(writeAddress)) continue;
        
            UINT32 value8bits = EXTRACTBYTE(value, byteNbr);  
            
            // 1er cas : valeur = 0 :  aucun changement
            if  (!value8bits) continue;         

            // 2eme cas : valeur 0xff => démarquage (OR x, 0xff = tjs 0xff)
            else if (value8bits == 0xff)    pTmgrGlobal->unTaintMemory<8>(writeAddress);
            
            // sinon, marquage du résultat avec opération "OR"
            else  pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                    ObjectSource(8, value8bits)));
        }   
    }
} // sOR_IM

template<UINT32 len> void LOGICAL::sOR_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags();
    else if (value == minusOne<len>::get()) // OR x, 0xff = 0xff, donc démarquage destination et flags
    {
        pTmgrTls->unTaintAllFlags();
        pTmgrTls->unTaintRegister<len>(reg);
    }
    else 
    {
        _LOGTAINT("orIR");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_OR,
            ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue)),
            ObjectSource(len, value)));

        // MARQUAGE DE LA DESTINATION
        REGINDEX regIndex = getRegIndex(reg);
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {
            // dest non marquée : ne rien faire
            if (!pTmgrTls->isRegisterPartTainted(regIndex, regPart)) continue;
        
            UINT32 value8bits = EXTRACTBYTE(value, regPart);

            // 1er cas : valeur = 0 : aucun changement
            if  (!value8bits) continue; 

            // 2eme cas : valeur nulle => démarquage (OR x, 0xff = tjs 0xff)
            else if (value8bits == 0xff) pTmgrTls->unTaintRegisterPart(regIndex, regPart);

            // sinon, marquage du résultat avec opération "OR"
            else 
            { 
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart)),  
                    ObjectSource(8, value8bits)));
            }
        }
    }
} // OR_IR

template<UINT32 len> void LOGICAL::sOR_RM
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT destValue = getMemoryValue<len>(writeAddress);

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    // cf tableau démarquage Flags sur le OR
    if (!isDestTainted && (!isSrcTainted || (destValue == minusOne<len>::get()))) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    else if ( !isSrcTainted && (srcValue == minusOne<len>::get()))
    {
        pTmgrTls->unTaintAllFlags();
        if (isDestTainted) pTmgrGlobal->unTaintMemory<len>(writeAddress);
    }
    else 
    {
        // dans tous les autres cas, marquage d'abord des flags puis destination octet par octet
        _LOGTAINT("orRM" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 
        
        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)) 
            : ObjectSource(len, destValue);

        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_OR,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION
        // plusieurs cas selon le marquage des opérandes, cf tableau OR 
        REGINDEX regSrcIndex = getRegIndex(regSrc);
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++writeAddress) 
        {   
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, byteNbr);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, byteNbr);
            bool isSrc8bitsTainted  = pTmgrTls->isRegisterPartTainted(regSrcIndex, byteNbr);
            bool isDest8bitsTainted = pTmgrGlobal->isMemoryTainted<8>(writeAddress);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue; 

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : dest = 0xff ; (OR 0xff, src) = 0xff, donc go on (dest déjà démarquée)
                if (dest8bitsValue == 0xff) continue;
                // cas 2.2 : destination vaut 0 ; (OR 0, src) équivaut à MOV dest, src
                else if (!dest8bitsValue) 
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr))));
                }
                // cas 2.3 : autres valeur de la destination => marquage via OR
                else
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_OR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr)),
                        ObjectSource(8, dest8bitsValue)));
                }
            }

            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0xff ; (OR dest, 0xff = 0xff) donc démarquer destination
                if (src8bitsValue == 0xff) pTmgrGlobal->unTaintMemory<8>(writeAddress);
                // cas 3.2 : src vaut 0 ; (OR dest, 0) ne modifie pas dest => continuer
                else if (!src8bitsValue) continue;
                // cas 3.3 : autres valeur de la source => marquage via OR
                else pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_OR,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                        ObjectSource(8, src8bitsValue)));                      
            }

            // CAS 4 : source et destination marquées => marquage via OR
            else 
            {
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr))));
            }
        }
    }
} // sOR_RM

template<UINT32 len> void LOGICAL::sOR_MR
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT srcValue = getMemoryValue<len>(readAddress);

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted  = pTmgrGlobal->isMemoryTainted<len>(readAddress);
    
    // cf tableau démarquage Flags sur le OR
    if (!isDestTainted && (!isSrcTainted || (destValue == minusOne<len>::get()))) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    else if ( !isSrcTainted && (srcValue == minusOne<len>::get()))
    {
        pTmgrTls->unTaintAllFlags();
        if (isDestTainted) pTmgrTls->unTaintRegister<len>(regSrcDest);
    }
    else 
    {
        // dans tous les autres cas, marquage d'abord des flags, puis destination octet par octet
        _LOGTAINT("orMR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_OR,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION, octet par octet
        // plusieurs cas selon le marquage des opérandes, cf tableau OR
        
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++readAddress) 
        {   
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, byteNbr);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, byteNbr);
            bool isSrc8bitsTainted  = pTmgrGlobal->isMemoryTainted<8>(readAddress);
            bool isDest8bitsTainted = pTmgrTls->isRegisterPartTainted(regSrcDestIndex, byteNbr);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;  

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : dest = 0xff ; (OR 0xff, src) = 0xff, donc go on (dest déjà démarquée)
                if (dest8bitsValue == 0xff) continue;
                // cas 2.2 : destination vaut 0 ; (OR 0, src) équivaut à MOV dest, src
                else if (!dest8bitsValue) 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
                }
                // cas 2.3 : autres valeur de la destination => marquage via OR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_OR,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),
                        ObjectSource(8, dest8bitsValue)));
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0xff ; (OR dest, 0xff) = 0xff, donc démarquer destination
                if (src8bitsValue == 0xff) pTmgrTls->unTaintRegisterPart(regSrcDestIndex, byteNbr);
                // cas 3.2 : src vaut 0 ; (OR dest, 0) ne modifie pas dest => continuer
                else if (!src8bitsValue) continue;
                // cas 3.3 : autres valeur de la source => marquage via OR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_OR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr)),
                        ObjectSource(8, src8bitsValue)));    
                }                                   
            }
            // CAS 4 : source et destination marquées => marquage via OR
            else 
            {
                pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr)),
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
            }   
        }
    }
} // end sOR_MR

template<UINT32 len> void LOGICAL::sOR_RR
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    // cf tableau démarquage Flags sur le OR
    if (!isDestTainted && (!isSrcTainted || (destValue == minusOne<len>::get()))) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    else if ( !isSrcTainted && (srcValue == minusOne<len>::get()))
    {
        pTmgrTls->unTaintAllFlags();
        if (isDestTainted) pTmgrTls->unTaintRegister<len>(regSrcDest);
    }
    else 
    {
        _LOGTAINT("orRR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
             // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_OR,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION
        // plusieurs cas selon le marquage des opérandes, cf tableau OR
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        REGINDEX regSrcIndex     = getRegIndex(regSrc);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {  
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, regPart);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, regPart);
            bool isSrc8bitsTainted  = pTmgrTls->isRegisterPartTainted(regSrcIndex, regPart);
            bool isDest8bitsTainted = pTmgrTls->isRegisterPartTainted(regSrcDestIndex, regPart);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : dest = 0 => (OR 0xff, src) = 0xff donc go on (dest déjà démarquée)
                if (dest8bitsValue == 0xff) continue;
                // cas 2.2 : destination vaut 0 ; (OR 0, src) équivaut à MOV dest, src
                else if (!dest8bitsValue)
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart))));
                }
                // cas 2.3 : autres valeur de la destination => marquage via OR
                else
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_OR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart)),
                        ObjectSource(8, dest8bitsValue)));
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0xff => (OR dest, 0xff = 0xff) donc démarquer destination
                if (src8bitsValue == 0xff)  pTmgrTls->unTaintRegisterPart(regSrcDestIndex, regPart);
                // cas 3.2 : src vaut 0 ; (OR dest, 0) ne modifie pas dest => continuer
                else if (!src8bitsValue) continue;
                // cas 3.3 : autres valeur de la source => marquage via OR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_OR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart)),
                        ObjectSource(8, src8bitsValue)));     
                }                                   
            }
            // CAS 4 : source et destination marquées => marquage via OR
            else 
            {
                pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart)),
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart)))); 
            }   
        }
    }
} // sOR_RR

///////////////
///// XOR /////
///////////////

// SIMULATE
template<UINT32 len> void LOGICAL::sXOR_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrGlobal->isMemoryTainted<len>(writeAddress)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorIM" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_XOR,
            ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)),
            ObjectSource(len, value)));

        // MARQUAGE DE LA DESTINATION, par octet pour éviter surmarquage
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++writeAddress)
        {
            // dest non marquée : ne rien faire
            if (!pTmgrGlobal->isMemoryTainted<8>(writeAddress)) continue;
        
            UINT32 value8bits = EXTRACTBYTE(value, byteNbr);  
            
            // 1er cas : valeur = 0 :  aucun changement
            if  (!value8bits) continue;         
            else 
            {
                ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(writeAddress));

                // 2eme cas : valeur 0xff => NOT de la destination (XOR x, 0xff = NOT x)
                if (value8bits == 0xff) 
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_NOT,
                        objSrcMem));
                }
                // sinon, marquage du résultat avec opération "XOR"
                else 
                {   
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                        ObjectSource(8, value8bits)));
                }
            }
        }   
    }
} // sXOR_IM

template<UINT32 len> void LOGICAL::sXOR_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorIR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_XOR,
            ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue)),
            ObjectSource(len, value)));

        // MARQUAGE DE LA DESTINATION
        REGINDEX regIndex = getRegIndex(reg);
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {
            // dest non marquée : ne rien faire
            if (!pTmgrTls->isRegisterPartTainted(regIndex, regPart)) continue;
            
             UINT32 value8bits = EXTRACTBYTE(value, regPart);
             // 1er cas : valeur = 0 :  aucun changement
            if  (!value8bits) continue; 
            else 
            {   
                ObjectSource objSrcReg(pTmgrTls->getRegisterPartTaint(regIndex, regPart));

                // 2eme cas : valeur 0xff => NOT de la destination (XOR x, 0xff = NOT x)
                if (value8bits == 0xff) 
                {
                    pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                        X_NOT,
                        objSrcReg));
                }
                // sinon, marquage du résultat avec opération "XOR"
                else 
                { 
                    pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart)),  
                        ObjectSource(8, value8bits)));
                }
            }
        }
    }
} // sXOR_IR

template<UINT32 len> void LOGICAL::sXOR_RM
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT destValue = getMemoryValue<len>(writeAddress);

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    if (!(isSrcTainted || isDestTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        // dans tous les autres cas, marquage d'abord des flags puis destination octet par octet
        _LOGTAINT("xorRM" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 
        
        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)) 
            : ObjectSource(len, destValue);

        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_XOR,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION
        // plusieurs cas selon le marquage des opérandes, cf tableau XOR    
        REGINDEX regSrcIndex = getRegIndex(regSrc);
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++writeAddress) 
        {   
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, byteNbr);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, byteNbr);
            bool isSrc8bitsTainted  = pTmgrTls->isRegisterPartTainted(regSrcIndex, byteNbr);
            bool isDest8bitsTainted = pTmgrGlobal->isMemoryTainted<8>(writeAddress);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;   

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : destination vaut 0 ; (XOR 0, src) équivaut à MOV dest, src
                if (!dest8bitsValue)
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr))));
                }
                // cas 2.2 : dest = 0xff ; XOR 0xff, src équivaut à NOT src, affecté à la dest
                else if (dest8bitsValue == 0xff) 
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_NOT,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr))));
                }
                // cas 2.3 : autres valeurs destination => marquage via XOR
                else
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr)),
                        ObjectSource(8, dest8bitsValue)));  
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0 ; (XOR dest, 0) ne modifie pas dest => continuer
                if (!src8bitsValue)  continue;
                // cas 3.2 : src vaut 0xff ; (XOR dest, 0xff) équivaut à NOT dest
                else if (src8bitsValue == 0xff) 
                {
                    pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_NOT,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress))));
                }
                // cas 3.3 : autres valeurs source => marquage via XOR
                else  pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),
                        ObjectSource(8, src8bitsValue)));
            }
            // CAS 4 : source et destination marquées => marquage via XOR
            else 
            {
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress)),  
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, byteNbr))));
            }   
        }
    }
} // sXOR_RM

template<UINT32 len> void LOGICAL::sXOR_MR
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT srcValue = getMemoryValue<len>(readAddress);

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted  = pTmgrGlobal->isMemoryTainted<len>(readAddress);
        
    // cf tableau démarquage Flags sur le XOR
    if (!(isSrcTainted || isDestTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorMR" << len << " ");
        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_XOR,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION, octet par octet
        // plusieurs cas selon le marquage des opérandes, cf tableau XOR
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        for (UINT32 byteNbr = 0 ; byteNbr < (len >> 3) ; ++byteNbr, ++readAddress) 
        {   
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, byteNbr);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, byteNbr);
            bool isSrc8bitsTainted  = pTmgrGlobal->isMemoryTainted<8>(readAddress);
            bool isDest8bitsTainted = pTmgrTls->isRegisterPartTainted(regSrcDestIndex, byteNbr);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;  

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : destination vaut 0 ; (XOR 0, src) équivaut à MOV dest, src
                if (!dest8bitsValue)
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
                } 
                // cas 2.2 : dest = 0xff ; (XOR 0xff, src) équivaut à NOT src, affecté à la dest
                else if (dest8bitsValue == 0xff) 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_NOT,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
                } 
                // cas 2.3 : autres valeurs destination => marquage via XOR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress)),
                        ObjectSource(8, dest8bitsValue)));
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0; (XOR dest, 0) ne modifie pas dest => continuer
                if (!src8bitsValue) continue;
                // cas 3.2 : src vaut 0xff ; (XOR dest, 0xff) équivaut à NOT dest
                else if (src8bitsValue == 0xff) 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_NOT,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr))));
                }
                // cas 3.3 : autres valeur source : marquage via XOR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr)),
                        ObjectSource(8, src8bitsValue)));    
                }                                   
            }
            // CAS 4 : source et destination marquées => marquage via XOR
            else 
            {
                pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, byteNbr, std::make_shared<TaintByte>(
                    X_OR,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, byteNbr)),
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
            }   
        }
    }
} // sXOR_RM

template<UINT32 len> void LOGICAL::sXOR_RR
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    // marquage de la totalité de la destination et de la source
    bool isDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    if ( !(isSrcTainted || isDestTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("xorRR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_XOR,
            objSrc,
            objSrcDest));

        // MARQUAGE DE LA DESTINATION
        // plusieurs cas selon le marquage des opérandes, cf tableau XOR
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        REGINDEX regSrcIndex     = getRegIndex(regSrc);

        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
        {  
            UINT32 src8bitsValue    = EXTRACTBYTE(srcValue, regPart);
            UINT32 dest8bitsValue   = EXTRACTBYTE(destValue, regPart);
            bool isSrc8bitsTainted  = pTmgrTls->isRegisterPartTainted(regSrcIndex, regPart);
            bool isDest8bitsTainted = pTmgrTls->isRegisterPartTainted(regSrcDestIndex, regPart);

            // CAS 1 : destination et sources non marquées => continuer pour prochain octet
            if (!(isDest8bitsTainted || isSrc8bitsTainted)) continue;  

            // CAS 2 : destination non marquée (et donc source marquée)
            else if (!isDest8bitsTainted) 
            {
                // cas 2.1 : destination vaut 0 ; (XOR 0, src) équivaut à MOV dest, src
                if (!dest8bitsValue) 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_ASSIGN,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart))));   
                }
                // cas 2.2 : dest = 0xff ; (XOR 0xff, src) équivaut à NOT src, affecté à la dest
                else if (dest8bitsValue == 0xff)
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_NOT,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart))));   
                }
                // cas 2.3 : autres valeurs destination => marquage via XOR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart)),
                        ObjectSource(8, dest8bitsValue)));    
                }
            }
            // CAS 3 : source non marquée (et donc destination marquée)
            else if (!isSrc8bitsTainted) 
            {
                // cas 3.1 : src vaut 0 ; (XOR dest, 0) ne modifie pas dest => continuer
                if (!src8bitsValue)  continue;
                // cas 3.2 : src vaut 0xff ; (XOR dest, 0xff) équivaut à NOT dest
                else if (src8bitsValue == 0xff) 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_NOT,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart))));   
                }
                // cas 3.3 : autres valeur de la source => marquage via XOR
                else 
                {
                    pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                        X_XOR,
                        ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart)),
                        ObjectSource(8, src8bitsValue)));    
                }                                   
            }
            // CAS 4 : source et destination marquées => marquage via XOR
            else 
            {
                pTmgrTls->updateTaintRegisterPart(regSrcDestIndex, regPart, std::make_shared<TaintByte>(
                    X_XOR,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, regPart)),
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcIndex, regPart))));  
            }   
        }
    }
} // end sXOR_RR

template<UINT32 len> void PIN_FAST_ANALYSIS_CALL LOGICAL::sXOR_RR_EQUAL(THREADID tid, REG reg ADDRESS_DEBUG) 
{
    // cas typique xor reg, reg => démarquage registre et flags 
    #if DEBUG
    PIN_GetLock(&g_lock, 0);
    g_taint << hexstr(insAddress) << " XOR_RR_EQUAL => demarquage !! \n"; 
    PIN_ReleaseLock(&g_lock);   
    #endif

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    pTmgrTls->unTaintAllFlags();
    pTmgrTls->unTaintRegister<len>(reg);
} // sXOR_RR_EQUAL

////////////////
///// TEST /////
////////////////

// SIMULATE
template<UINT32 len> void LOGICAL::sTEST_IM(THREADID tid, ADDRINT value, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(writeAddress) || (value == 0)) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    else 
    {
        _LOGTAINT("testIM" << len << " ");
        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)),
            ObjectSource(len, value)));
    }
} // sTEST_IM

template<UINT32 len> void LOGICAL::sTEST_IR(THREADID tid, ADDRINT value, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if ( !pTmgrTls->isRegisterTainted<len>(reg) || (value == 0)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("testIR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue)),
            ObjectSource(len, value)));
    }
} // sTEST_IR

template<UINT32 len> void LOGICAL::sTEST_RM
    (THREADID tid, REG regSrc, ADDRINT srcValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT destValue = getMemoryValue<len>(writeAddress);

    // marquage de la totalité de la destination et de la source
    bool isFullDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    bool isFullSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    // cas particuliers du AND (cf tableau, avec simplification par loi Morgan)
    /* if ((!isFullDestTainted && !isFullSrcTainted) \
        || (!isFullDestTainted && !destValue) \
        || (!isFullSrcTainted && !srcValue) ) => 11 opérations */
    //  (!a && !b) || (!a && !c) || (!b || !d) <=> ( !(a && (b || d) || (b && c))
    //  PLUS QUE 5 OPERATIONS                                       
    if (!((isFullDestTainted && (isFullSrcTainted || (srcValue != 0))) || (isFullSrcTainted && (destValue != 0)))) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    
    else // dans tous les autres cas, marquage des flags 
    { 
        _LOGTAINT("testRM" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isFullSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isFullDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress)) 
            : ObjectSource(len, destValue);

        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            objSrc,
            objSrcDest)); 
    }
} // sTEST_RM

template<UINT32 len> void LOGICAL::sTEST_MR
    (THREADID tid, ADDRINT readAddress, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    ADDRINT srcValue = getMemoryValue<len>(readAddress);

    bool isFullDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest); 
    bool isFullSrcTainted  = pTmgrGlobal->isMemoryTainted<len>(readAddress);
    
    // cas particuliers du AND (cf tableau, avec simplification par loi Morgan)
    /* if ((!isFullDestTainted && !isFullSrcTainted) \
        || (!isFullDestTainted && !destValue) \
        || (!isFullSrcTainted && !srcValue) ) => 11 opérations */
    //  (!a && !b) || (!a && !c) || (!b || !d) <=> ( !(a && (b || d) || (b && c))
    //  PLUS QUE 5 OPERATIONS                                       
    if (!((isFullDestTainted && (isFullSrcTainted || (srcValue != 0))) || (isFullSrcTainted && (destValue != 0)))) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    else 
    {
        _LOGTAINT("testMR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isFullSrcTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(readAddress))
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isFullDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            objSrc,
            objSrcDest));
    }
} // sTEST_MR

template<UINT32 len> void LOGICAL::sTEST_RR
    (THREADID tid, REG regSrc, ADDRINT srcValue, REG regSrcDest, ADDRINT destValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    bool isFullDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest); 
    bool isFullSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    // cas particuliers du AND (cf tableau, avec simplification par loi Morgan)
    /* if ((!isFullDestTainted && !isFullSrcTainted) \
        || (!isFullDestTainted && !destValue) \
        || (!isFullSrcTainted && !srcValue) ) => 11 opérations */
    //  (!a && !b) || (!a && !c) || (!b || !d) <=> ( !(a && (b || d) || (b && c))
    //  PLUS QUE 5 OPERATIONS                                       
    if (!((isFullDestTainted && (isFullSrcTainted || (srcValue != 0))) || (isFullSrcTainted && (destValue != 0)))) 
    {
        pTmgrTls->unTaintAllFlags();
    }
    else 
    {
        _LOGTAINT("testRR" << len << " ");

        // MARQUAGE DES FLAGS, dépendant uniquement du résultat 

        // source 1 : source
        ObjectSource objSrc = (isFullSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, srcValue)) 
            : ObjectSource(len, srcValue);
        
        // source 2 : source/destination
        ObjectSource objSrcDest = (isFullDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, destValue)) 
            : ObjectSource(len, destValue);
        
        fTaintLOGICAL(pTmgrTls, std::make_shared<TaintObject<len>>(
            X_AND,
            objSrc,
            objSrcDest));
    }
} // sTEST_RR

template<UINT32 len> void LOGICAL::sTEST_RR_EQUAL(THREADID tid, REG regSrc, ADDRINT srcValue ADDRESS_DEBUG) 
{
    // cas particulier des registres égaux : moins d'arguments passés
    // et marquage des flags simplifié
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (!pTmgrTls->isRegisterTainted<len>(regSrc))  pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("testRR_EQUAL" << len << " ");

        // marquage des flags avec la source uniquement (AND a, a = a)
        fTaintLOGICAL(pTmgrTls, pTmgrTls->getRegisterTaint<len>(regSrc, srcValue));
    }
} // sTEST_RR_EQUAL

///////////////
///// NOT /////
///////////////

// SIMULATE
template<UINT32 len> void LOGICAL::sNOT_M(ADDRINT writeAddress ADDRESS_DEBUG) 
{
    // pas besoin du thread (rien sur les flags ni registres)
    if (pTmgrGlobal->isMemoryTainted<len>(writeAddress)) 
    {
        _LOGTAINT("notM" << len << " ");
        ADDRINT lastAddress = writeAddress + (len >> 3);
        do
        {   
            // si octet marqué, marquage dest = NOT(dest), sinon rien
            if (pTmgrGlobal->isMemoryTainted<8>(writeAddress)) 
            {   
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddress))));
            }
        } while (++writeAddress < lastAddress);
    }
} // sNOT_M

template<UINT32 len> void LOGICAL::sNOT_R(THREADID tid, REG reg ADDRESS_DEBUG) 
{
    // masque binaire du marquage de la source
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    if (pTmgrTls->isRegisterTainted<len>(reg)) // si registre marqué
    {
        _LOGTAINT("notR");
        REGINDEX regIndex = getRegIndex(reg);
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart)       
        {
            // si octet marqué, marquage dest = NOT(dest)
            if (pTmgrTls->isRegisterPartTainted(regIndex, regPart))   
            {   
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    X_NOT,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart))));
            }
        }
    }
} // sNOT_R
