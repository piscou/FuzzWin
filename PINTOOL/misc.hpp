// SIMULATE

#if TARGET_IA32
// BASE + DISPL : BD
template<UINT32 lenEA, UINT32 lenDest> 
void MISC::sLEA_BD(THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, INT32 displ ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // traitement ssi le registre de base est marqué 
    if (pTmgrTls->isRegisterTainted<32>(baseReg)) 
    {
        TaintDwordPtr eaPtr;
        // déplacement nul : récupération du marquage du registre
        if (!displ) eaPtr = pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue);
        else // sinon, construction de l'objet ISD        
        {
            // addition ou soustraction selon signe du déplacement
            eaPtr = std::make_shared<TaintDword>(
                (displ > 0) ? X_ADD : X_SUB, 
                ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue)),
                ObjectSource(32, abs(displ)));
        }
        
        _LOGTAINT("leaBD EA" << lenEA << "bits Destination " << lenDest << "bits valeur displ " << displ);
        taintLEA(pTmgrTls, regDest, lenEA, lenDest, eaPtr);
    }
    // si registre de base non marqué, démarquer la destination
    else pTmgrTls->unTaintRegister<lenDest>(regDest);
} // sLEA_BD

// INDEX + SCALE + DISPL : ISD
template<UINT32 lenEA, UINT32 lenDest> 
void MISC::sLEA_ISD(THREADID tid, REG regDest, REG indexReg, ADDRINT indexRegValue, 
                    UINT32 scale, INT32 displ ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // traitement ssi le registre d'index est marqué 
    if (pTmgrTls->isRegisterTainted<32>(indexReg)) 
    {
        // 1) traitement de l'opération index*scale
        TaintDwordPtr tdw_IS_ptr;

        // pas de scale => index tout court
        if (scale == 1)  tdw_IS_ptr = pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue);
        else // cas Scale = 2, 4 ou 8
        { 
            // valeur du déplacement (avec scale = 2^depl)
            UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3); 
            // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
            // source 1 : le registre d'index (forcément marqué)
            // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
            tdw_IS_ptr = std::make_shared<TaintDword>(
                X_SHL, 
                ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)),
                ObjectSource(8, shiftValue));   
        }

        // construction de l'EA définitive
        TaintDwordPtr eaPtr;
        // si déplacement nul, resultat vaut la valeur de IS
        if (!displ)  eaPtr = tdw_IS_ptr;
        // sinon, construction de l'objet ISD
        else 
        {
            // addition ou soustraction selon signe du déplacement
            eaPtr = std::make_shared<TaintDword>(
                (displ > 0) ? X_ADD : X_SUB, 
                ObjectSource(tdw_IS_ptr),
                ObjectSource(32, abs(displ)));
        }
 
        // marquage de la destination
        _LOGTAINT("leaISD EA" << lenEA << "bits Destination " << lenDest << "bits");
        taintLEA(pTmgrTls, regDest, lenEA, lenDest, eaPtr);
    }
    // sinon démarquage de la destination
    else pTmgrTls->unTaintRegister<lenDest>(regDest);
} // sLEA_ISD

// BASE + INDEX + SCALE + DISPL : BISD
template<UINT32 lenEA, UINT32 lenDest> 
void MISC::sLEA_BISD(THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, 
                     REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<32>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<32>(baseReg);

    // il faut au moins un des registres marqués, sinon démarquage destination
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintDword taintEA(
            X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue))
                               : ObjectSource(32, baseRegValue));  
    
        // ajout d'index*scale +/- displ (SOURCE 2), selon son marquage 
        if (isIndexRegTainted) 
        {      
            // 1) traitement de l'opération index*scale
            TaintDwordPtr tdw_IS_ptr;
            if (scale == 1)  tdw_IS_ptr = pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue);
            else // cas Scale = 2, 4 ou 8
            { 
                // valeur du déplacement (avec scale = 2^depl)
                UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3); 
                // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
                // source 1 : le registre d'index (forcément marqué)
                // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
                tdw_IS_ptr = std::make_shared<TaintDword>
                    (X_SHL, 
                    ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)),
                    ObjectSource(8, shiftValue));  
            }
            
            // 2) traitement du déplacement, et ajout de la source2 au resultat
            // si pas de déplacement, source2 vaut la valeur de IS
            if (!displ) taintEA.addSource(tdw_IS_ptr);   
            else // sinon, construction de l'objet ISD
            {
                // addition ou soustraction selon signe du déplacement
                // et ajout comme source2 au résultat
                taintEA.addSource(std::make_shared<TaintDword>( 
                    (displ > 0) ? X_ADD : X_SUB, 
                    ObjectSource(tdw_IS_ptr),
                    ObjectSource(32, abs(displ))));  
                // ajout comme source2 au résultat
            }
        }
        else taintEA.addConstantAsASource<32>(indexRegValue * scale + displ);

        // marquage de la destination
        _LOGTAINT("leaBISD EA" << lenEA << "bits Destination " << lenDest << "bits");
        taintLEA(pTmgrTls, regDest, lenEA, lenDest, std::make_shared<TaintDword>(taintEA));
    }   
    // sinon démarquage de la destination
    else pTmgrTls->unTaintRegister<lenDest>(regDest);
} // sLEA_BISD

#else

// BASE + DISPL : BD
template<UINT32 lenEA, UINT32 lenDest> 
void MISC::sLEA_BD(THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, INT32 displ ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // traitement si le registre de base est marqué 
    if (pTmgrTls->isRegisterTainted<64>(baseReg)) 
    {
        TaintQwordPtr eaPtr;
        // déplacement nul : récupération du marquage du registre
        if (!displ) eaPtr = pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue);
        else // sinon, construction de l'objet ISD        
        {
            // addition ou soustraction selon signe du déplacement
            eaPtr = std::make_shared<TaintQword>(
                (displ > 0) ? X_ADD : X_SUB, 
                ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue)),
                ObjectSource(64, abs(displ)));
        }
        
        _LOGTAINT("leaBD EA" << lenEA << "bits Destination " << lenDest << "bits valeur displ " << displ);
        taintLEA(pTmgrTls, regDest, lenEA, lenDest, eaPtr);
    }
    // si registre de base non marqué, démarquer la destination
    else pTmgrTls->unTaintRegister<lenDest>(regDest);
} // sLEA_BD

// INDEX + SCALE + DISPL : ISD
template<UINT32 lenEA, UINT32 lenDest> 
void MISC::sLEA_ISD(THREADID tid, REG regDest, REG indexReg, ADDRINT indexRegValue, 
                    UINT32 scale, INT32 displ ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // traitement ssi le registre d'index est marqué 
    if (pTmgrTls->isRegisterTainted<64>(indexReg)) 
    {
        // 1) traitement de l'opération index*scale
        TaintQwordPtr tqw_IS_ptr;

        // pas de scale => index tout court
        if (scale == 1)  tqw_IS_ptr = pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue);
        else // cas Scale = 2, 4 ou 8
        { 
            // valeur du déplacement (avec scale = 2^depl)
            UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3); 
            // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
            // source 1 : le registre d'index (forcément marqué)
            // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
            tqw_IS_ptr = std::make_shared<TaintQword>
                (X_SHL, 
                ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)),
                ObjectSource(8, shiftValue));   
        }

        // construction de l'EA définitive
        TaintQwordPtr eaPtr;
        // si déplacement nul, resultat vaut la valeur de IS
        if (!displ)  eaPtr = tqw_IS_ptr;
        // sinon, construction de l'objet ISD
        else 
        {
            // addition ou soustraction selon signe du déplacement
            eaPtr = std::make_shared<TaintQword>(
                (displ > 0) ? X_ADD : X_SUB, 
                ObjectSource(tqw_IS_ptr),
                ObjectSource(64, abs(displ)));
        }
 
        // marquage de la destination
        _LOGTAINT("leaISD EA" << lenEA << "bits Destination " << lenDest << "bits");
        taintLEA(pTmgrTls, regDest, lenEA, lenDest, eaPtr);
    }
    // sinon démarquage de la destination
    else pTmgrTls->unTaintRegister<lenDest>(regDest);
} // sLEA_ISD

// BASE + INDEX + SCALE + DISPL : BISD
template<UINT32 lenEA, UINT32 lenDest> 
void MISC::sLEA_BISD(THREADID tid, REG regDest, REG baseReg, ADDRINT baseRegValue, 
                     REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<64>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<64>(baseReg);

    // il faut au moins un des registres marqués, sinon démarquage destination
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintQword taintEA(
            X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue))
                               : ObjectSource(64, baseRegValue));  
    
        // ajout d'index*scale +/- displ (SOURCE 2), selon son marquage 
        if (isIndexRegTainted) 
        {      
            // 1) traitement de l'opération index*scale
            TaintQwordPtr tqw_IS_ptr;
            if (scale == 1)  tqw_IS_ptr = pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue);
            else // cas Scale = 2, 4 ou 8
            { 
                // valeur du déplacement (avec scale = 2^depl)
                UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3); 
                // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
                // source 1 : le registre d'index (forcément marqué)
                // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
                tqw_IS_ptr = std::make_shared<TaintQword>
                    (X_SHL, 
                    ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)),
                    ObjectSource(8, shiftValue));  
            }
            
            // 2) traitement du déplacement, et ajout de la source2 au resultat
            // si pas de déplacement, source2 vaut la valeur de IS
            if (!displ) taintEA.addSource(tqw_IS_ptr);   
            else // sinon, construction de l'objet ISD
            {
                // addition ou soustraction selon signe du déplacement
                // et ajout comme source2 au résultat
                taintEA.addSource(std::make_shared<TaintQword>( 
                    (displ > 0) ? X_ADD : X_SUB, 
                    ObjectSource(tqw_IS_ptr),
                    ObjectSource(64, abs(displ))));  
                // ajout comme source2 au résultat
            }
        }
        else taintEA.addConstantAsASource<64>(indexRegValue * scale + displ);

        // marquage de la destination
        _LOGTAINT("leaBISD EA" << lenEA << "bits Destination " << lenDest << "bits");
        taintLEA(pTmgrTls, regDest, lenEA, lenDest, std::make_shared<TaintQword>(taintEA));
    }   
    // sinon démarquage de la destination
    else pTmgrTls->unTaintRegister<lenDest>(regDest);
} // sLEA_BISD
#endif
