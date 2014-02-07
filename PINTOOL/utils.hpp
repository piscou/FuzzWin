template<UINT32 len> void PIN_FAST_ANALYSIS_CALL UTILS::uREG(REG reg) 
{ 
    pTmgr->unTaintRegister<len>(reg); 
}

template<UINT32 len> void PIN_FAST_ANALYSIS_CALL UTILS::uMEM(ADDRINT address) 
{ 
    pTmgr->unTaintMemory<len>(address); 
}
        
#if TARGET_IA32
TaintDwordPtr UTILS::computeEA_BISD(REG baseReg, ADDRINT baseRegValue, 
    REG indexReg, ADDRINT indexRegValue, INT32 displ, UINT32 scale)
{
// pour construire l'EA, on additionne deux objets : la base, et (index*scale+displ)
//  SI BASE MARQUEE source1 = marquage base
//  SINON source1 = valeur registre de base
//
//  SI INDEX MARQUE 
//      SI = index*scale (via SHL)
//      SI DISPL NON NUL
//          ISD = IS +/- displ (via ADD ou SUB)
//          source2 = ISD
//      SINON source2 = IS
//  SINON source2 = valeur (index*scale +/- displ)

    bool isIndexRegTainted = pTmgr->isRegisterTainted<32>(indexReg);
    bool isBaseRegTainted =  pTmgr->isRegisterTainted<32>(baseReg);
    // l'un au moins des registres est marqué (sinon on n'aurait pas du appeler la fonction...)
#if DEBUG
    if (!(isIndexRegTainted || isBaseRegTainted)) return nullptr;
#endif

    TaintDwordPtr result = std::make_shared<TaintDword>(X_ADD);  
    
    // ajout de la base, selon son marquage
    if (isBaseRegTainted)  result->addSource(pTmgr->getRegisterTaint<32>(baseReg, baseRegValue));  
    else result->addValueAsASource<32>(baseRegValue);

    // ajout d'index*scale +/- displ, selon son marquage 
    if (isIndexRegTainted) 
    {      
        // 1) traitement de l'opération index*scale
        TaintDwordPtr tdw_IS_Ptr;
        if (scale == 1)  tdw_IS_Ptr = pTmgr->getRegisterTaint<32>(indexReg, indexRegValue);
        else // cas Scale = 2, 4 ou 8
        { 
            // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
            tdw_IS_Ptr = std::make_shared<TaintDword>(X_SHL);  
            // source 1 : le registre d'index (forcément marqué)
            tdw_IS_Ptr->addSource(pTmgr->getRegisterTaint<32>(indexReg, indexRegValue));  
            // source 2 : valeur du déplacement (avec scale = 2^depl)
            tdw_IS_Ptr->addValueAsASource<8>((scale == 2) ? 1 : ((scale == 4) ? 2 : 3));  
        }
        // 2) traitement du déplacement, et ajout de la source2 au resultat
        // si pas de déplacement, source2 vaut la valeur de IS
        if (!displ) result->addSource(tdw_IS_Ptr);   
        else // sinon, construction de l'objet ISD
        {
            // addition ou soustraction selon signe du déplacement
            TaintDwordPtr tdw_ISD_Ptr = std::make_shared<TaintDword>((displ > 0) ? X_ADD : X_SUB);  
            tdw_ISD_Ptr->addSource(tdw_IS_Ptr);  
            tdw_ISD_Ptr->addValueAsASource<32>(abs(displ));
            // ajout comme source2 au résultat
            result->addSource(tdw_ISD_Ptr);
        }
    }
    else result->addValueAsASource<32>(indexRegValue*scale + displ);

    return (result);
} // computeEA_BISD
  
TaintDwordPtr UTILS::computeEA_ISD(REG indexReg, ADDRINT indexRegValue, INT32 displ, UINT32 scale)
{ 
//  SI = index*scale (via SHL)
//  SI DISPL NON NUL
//      ISD = IS +/- displ (via ADD ou SUB)
//      resul = ISD
//  SINON result = IS

    // le registre est supposé marqué (sinon on n'aurait pas du appeler la fonction...)
#if DEBUG
    if (!pTmgr->isRegisterTainted<32>(indexReg)) return nullptr;
#endif

    TaintDwordPtr result = nullptr; 

    // 1) traitement de l'opération index*scale
    TaintDwordPtr tdw_IS_Ptr = nullptr;
    if (scale == 1)  tdw_IS_Ptr = pTmgr->getRegisterTaint<32>(indexReg, indexRegValue);
    else // cas Scale = 2, 4 ou 8
    { 
        // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
        tdw_IS_Ptr = std::make_shared<TaintDword>(X_SHL);  
        // source 1 : le registre d'index (forcément marqué)
        tdw_IS_Ptr->addSource(pTmgr->getRegisterTaint<32>(indexReg, indexRegValue));  
        // source 2 : valeur du déplacement (avec scale = 2^depl)
        tdw_IS_Ptr->addValueAsASource<8>((scale == 2) ? 1 : ((scale == 4) ? 2 : 3));  
    }
    // 2) traitement du déplacement, et construcion du resultat
    // si pas de déplacement, resultat vaut la valeur de IS
    if (!displ) result = tdw_IS_Ptr;   
    else // sinon, construction de l'objet ISD
    {
        // addition ou soustraction selon signe du déplacement
        TaintDwordPtr tdw_ISD_Ptr = std::make_shared<TaintDword>((displ > 0) ? X_ADD : X_SUB);  
        tdw_ISD_Ptr->addSource(tdw_IS_Ptr);  
        tdw_ISD_Ptr->addValueAsASource<32>(abs(displ));
        // ajout comme source2 au résultat
        result = tdw_ISD_Ptr;
    }
    return (result);
} // computeEA_ISD

TaintDwordPtr UTILS::computeEA_BD(REG baseReg, ADDRINT baseRegValue, INT32 displ)
{ 
    // le registre est supposé marqué (sinon on n'aurait pas du appeler la fonction...)
#if DEBUG
    if (!pTmgr->isRegisterTainted<32>(baseReg)) return nullptr;
#endif
    // on suppose que le déplacement est non nul, sinon cela fera une addition avec 0...
    TaintDwordPtr resultPtr = std::make_shared<TaintDword>((displ > 0) ? X_ADD : X_SUB);  
    resultPtr->addSource(pTmgr->getRegisterTaint<32>(baseReg, baseRegValue));  
    resultPtr->addValueAsASource<32>(abs(displ));
    return (resultPtr);
} // computeEA_BD
  
#else

TaintQwordPtr UTILS::computeEA_BISD(REG baseReg, ADDRINT baseRegValue, 
    REG indexReg, ADDRINT indexRegValue, INT32 displ, UINT32 scale)
{
// pour construire l'EA, on additionne deux objets : la base, et (index*scale+displ)
//  SI BASE MARQUEE source1 = marquage base
//  SINON source1 = valeur registre de base
//
//  SI INDEX MARQUE 
//      SI = index*scale (via SHL)
//      SI DISPL NON NUL
//          ISD = IS +/- displ (via ADD ou SUB)
//          source2 = ISD
//      SINON source2 = IS
//  SINON source2 = valeur (index*scale +/- displ)

    bool isIndexRegTainted = pTmgr->isRegisterTainted<64>(indexReg);
    bool isBaseRegTainted =  pTmgr->isRegisterTainted<64>(baseReg);
    // l'un au moins des registres est marqué (sinon on n'aurait pas du appeler la fonction...)
#if DEBUG
    if (!(isIndexRegTainted || isBaseRegTainted)) return nullptr;
#endif

    TaintQwordPtr result = std::make_shared<TaintQword>(X_ADD);  
    
    // ajout de la base, selon son marquage
    if (isBaseRegTainted)  result->addSource(pTmgr->getRegisterTaint<64>(baseReg, baseRegValue));  
    else result->addValueAsASource<64>(baseRegValue);

    // ajout d'index*scale +/- displ, selon son marquage 
    if (isIndexRegTainted) 
    {      
        // 1) traitement de l'opération index*scale
        TaintQwordPtr tqw_IS_Ptr;
        if (scale == 1)  tqw_IS_Ptr = pTmgr->getRegisterTaint<64>(indexReg, indexRegValue);
        else // cas Scale = 2, 4 ou 8
        { 
            // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
            tqw_IS_Ptr = std::make_shared<TaintQword>(X_SHL);  
            // source 1 : le registre d'index (forcément marqué)
            tqw_IS_Ptr->addSource(pTmgr->getRegisterTaint<64>(indexReg, indexRegValue));  
            // source 2 : valeur du déplacement (avec scale = 2^depl)
            tqw_IS_Ptr->addValueAsASource<8>((scale == 2) ? 1 : ((scale == 4) ? 2 : 3));  
        }
        // 2) traitement du déplacement, et ajout de la source2 au resultat
        // si pas de déplacement, source2 vaut la valeur de IS
        if (!displ) result->addSource(tqw_IS_Ptr);   
        else // sinon, construction de l'objet ISD
        {
            // addition ou soustraction selon signe du déplacement
            TaintQwordPtr tqw_ISD_Ptr = std::make_shared<TaintQword>((displ > 0) ? X_ADD : X_SUB);  
            tqw_ISD_Ptr->addSource(tqw_IS_Ptr);  
            tqw_ISD_Ptr->addValueAsASource<64>(abs(displ));
            // ajout comme source2 au résultat
            result->addSource(tqw_ISD_Ptr);
        }
    }
    else result->addValueAsASource<64>(indexRegValue*scale + displ);

    return (result);
} // computeEA_BISD
  
TaintQwordPtr UTILS::computeEA_ISD(REG indexReg, ADDRINT indexRegValue, INT32 displ, UINT32 scale)
{ 
//  SI = index*scale (via SHL)
//  SI DISPL NON NUL
//      ISD = IS +/- displ (via ADD ou SUB)
//      resul = ISD
//  SINON result = IS

    // le registre est supposé marqué (sinon on n'aurait pas du appeler la fonction...)
#if DEBUG
    if (!pTmgr->isRegisterTainted<64>(indexReg)) return nullptr;
#endif

    TaintQwordPtr result = nullptr; 

    // 1) traitement de l'opération index*scale
    TaintQwordPtr tqw_IS_Ptr = nullptr;
    if (scale == 1)  tqw_IS_Ptr = pTmgr->getRegisterTaint<64>(indexReg, indexRegValue);
    else // cas Scale = 2, 4 ou 8
    { 
        // nouvel objet index * scale, traité comme un SHL car déplacement multiple de 2 
        tqw_IS_Ptr = std::make_shared<TaintQword>(X_SHL);  
        // source 1 : le registre d'index (forcément marqué)
        tqw_IS_Ptr->addSource(pTmgr->getRegisterTaint<64>(indexReg, indexRegValue));  
        // source 2 : valeur du déplacement (avec scale = 2^depl)
        tqw_IS_Ptr->addValueAsASource<8>((scale == 2) ? 1 : ((scale == 4) ? 2 : 3));  
    }
    // 2) traitement du déplacement, et construcion du resultat
    // si pas de déplacement, resultat vaut la valeur de IS
    if (!displ) result = tqw_IS_Ptr;   
    else // sinon, construction de l'objet ISD
    {
        // addition ou soustraction selon signe du déplacement
        TaintQwordPtr tqw_ISD_Ptr = std::make_shared<TaintQword>((displ > 0) ? X_ADD : X_SUB);  
        tqw_ISD_Ptr->addSource(tqw_IS_Ptr);  
        tqw_ISD_Ptr->addValueAsASource<64>(abs(displ));
        // ajout comme source2 au résultat
        result = tqw_ISD_Ptr;
    }
    return (result);
} // computeEA_ISD

TaintQwordPtr UTILS::computeEA_BD(REG baseReg, ADDRINT baseRegValue, INT32 displ)
{ 
    // le registre est supposé marqué (sinon on n'aurait pas du appeler la fonction...)
#if DEBUG
    if (!pTmgr->isRegisterTainted<64>(baseReg)) return nullptr;
#endif
    // on suppose que le déplacement est non nul, sinon cela fera une addition avec 0...
    TaintQwordPtr resultPtr = std::make_shared<TaintQword>((displ > 0) ? X_ADD : X_SUB);  
    resultPtr->addSource(pTmgr->getRegisterTaint<64>(baseReg, baseRegValue));  
    resultPtr->addValueAsASource<64>(abs(displ));
    return (resultPtr);
} // computeEA_BD

#endif // TARGET_IA32