// SIMULATE
template<UINT32 len> void STRINGOP::sMOVS
    (ADDRINT count, ADDRINT flagsValue, ADDRINT readAddress, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    // copie de "count" octets/mot/double mots de [ESI] vers [EDI] (idem MOV mem->mem)
    ADDRINT nbIterations = count * (len >> 3); // nombre d'octets copiés
    
    // direction Flag mis à 1 : les adresses vont décroissantes, sinon ca sera l'inverse
    UINT32 isDecrease = (flagsValue >> DIRECTION_FLAG) & 1; 
    
    for (UINT32 counter = 0 ; counter < nbIterations; ++counter)
    {
        if (pTmgrGlobal->isMemoryTainted<8>(readAddress))	
        {
            _LOGTAINT("MOVS " << len<< "bits");
            pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                X_ASSIGN,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));
        }
        else pTmgrGlobal->unTaintMemory<8>(writeAddress);
            
        if (isDecrease)
        {
            --readAddress; --writeAddress;
        }
        else
        {
            ++readAddress; ++writeAddress;
        }
    }
} //sMOVS

template<UINT32 len> void STRINGOP::sLODS
    (THREADID tid, ADDRINT count, ADDRINT flagsValue, ADDRINT readAddress ADDRESS_DEBUG) 
{
    // déplacement de "count" octets/mot/dble mots de [ESI] vers AL/AX/EAX/RAX
    // en réalité, seule la dernière itération nous interesse
    // ce sera un MOV_MR<len> de lastAddress vers AL/AX/EAX/RAX
  
    // calcul de l'adresse pointée par ESI lors de la dernière opération
    // DF a 1 => adresses décroissantes, DF a 0 => adresses croissantes
    ADDRINT lastAddress = ((flagsValue >> DIRECTION_FLAG) & 1) 
        ? (readAddress - ((count-1) * (len >> 3))) 
        : (readAddress + ((count-1) * (len >> 3))); 
    
    // appel de la procédure MOVMR adéquate selon le registre
    _LOGTAINT("LODS (si marqué : message movRM suivra)");
    DATAXFER::sMOV_MR<len>(tid, lastAddress, registerACC<len>::getReg() INSADDRESS);
} // sLODS

template<UINT32 len> void STRINGOP::sSTOS
    (THREADID tid, ADDRINT count, ADDRINT flagsValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    // déplacement de "count" octets/mot/dble mots de AL/AX/EAX/RAX -> [EDI] 
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
        
    // 1) recupération du marquage du registre, et stockage dans un vecteur.
    // et stockage dans un tableau d'objets (ou nullPtr)
    vector<TaintBytePtr> vTaintRegSrc;
    for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart) 
    {
        #if TARGET_IA32
        vTaintRegSrc.push_back(pTmgrTls->getRegisterPartTaint(rEAX, regPart));
        #else
        vTaintRegSrc.push_back(pTmgrTls->getRegisterPartTaint(rRAX, regPart));
        #endif  
    }

    // si DF = 1 => adresses décroissantes, sinon le contraire
    UINT32 isDecrease = (flagsValue >> DIRECTION_FLAG) & 1; 

    for (UINT32 iteration = 0 ; iteration < count ; ++iteration) // répétition "count" fois
    {
        // marquage de chaque plage de 'len' octets avec le registre source     
        for (auto it = vTaintRegSrc.begin(); it != vTaintRegSrc.end() ; ++it) 
        {
            if ((bool) *it)
            {
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(*it)));
            }
            else pTmgrGlobal->unTaintMemory<8>(writeAddress);

            // calcul de la prochaine adresse
            (isDecrease) ? --writeAddress : ++writeAddress;
        }
    }
} // sSTOS

template<UINT32 len> void STRINGOP::sStoreTaintSCAS(
    THREADID tid, BOOL isREPZ, ADDRINT regValue, ADDRINT insAddress) 
{ 
    // procédure appelée lors de la première itération (callback IF/THEN)
    // sert à stocker dans TaintManager les arguments (marquage, adresse)
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    StringOpInfo strInfo = {0};

    // mise en cache de la valeur du préfixe (true = REPZ/E, false = REPNZ/E)
    strInfo.isREPZ = isREPZ; 
    
    // si registre marqué, stockage de l'objet, sinon mise à nullptr 
    // et stockage de la valeur
    if (pTmgrTls->isRegisterTainted<len>(registerACC<len>::getReg())) 
    {
        strInfo.isRegTainted = true;
        strInfo.tPtr = pTmgrTls->getRegisterTaint<len>(registerACC<len>::getReg(), regValue);
    }
    else 
    {
        strInfo.isRegTainted = false;
        strInfo.tPtr = nullptr;	 
        strInfo.regValue = regValue; // stockage de la valeur du registre
    }
    // mise en cache
    pTmgrTls->storeStringOpInfo(strInfo);
} // storeTaintSCAS

template<UINT32 len> void STRINGOP::sSCAS(THREADID tid, ADDRINT address) 
{
    // comparaison de AL/AX/EAX/RAX avec [EDI] 
    // + ajout d'une contrainte sur ZFLAG, indiquant une répétition ou non
    // métohde identique à CMP_MR, reprise ici intégralement afin d'insérer la contrainte sur le ZFLAG
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    StringOpInfo strInfo = pTmgrTls->getStoredStringOpInfo();
    
    bool isSrcDestTainted = strInfo.isRegTainted;
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<len>(address);

    if ( !(isSrcDestTainted || isSrcTainted))   pTmgrTls->unTaintAllFlags();
    else 
    {
        ADDRINT insAddress = strInfo.instrPtr; // adresse de l'ins (en cache)
        _LOGTAINT("SCAS");
        
        // calcul des sources pour le futur objet
        ObjectSource srcDest = (isSrcDestTainted) 
            ? ObjectSource(strInfo.tPtr) : ObjectSource(len, strInfo.regValue);
        
        ObjectSource src = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(address))
            : ObjectSource(len, getMemoryValue<len>(address));

        // marquage flags 
        BINARY::fTaintCMP<len>(pTmgrTls, srcDest, src);
        // déclaration de la contrainte
        pFormula->addConstraint_ZERO(pTmgrTls, insAddress, strInfo.isREPZ);
    }
} // sSCAS

template<UINT32 len> void STRINGOP::sCMPS
    (THREADID tid, UINT32 repCode, ADDRINT esiAddr, ADDRINT ediAddr, ADDRINT insAddress) 
{
    bool isSrcTainted =		pTmgrGlobal->isMemoryTainted<len>(esiAddr);
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(ediAddr);	
    
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(tlsKeyTaint, tid));
    
    if ( !(isSrcDestTainted || isSrcTainted)) pTmgrTls->unTaintAllFlags();
    else 
    {
        _LOGTAINT("CMPS");
        
        ObjectSource src = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(esiAddr))
            : ObjectSource(len, getMemoryValue<len>(esiAddr));
       
        ObjectSource srcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(ediAddr))
            : ObjectSource(len, getMemoryValue<len>(ediAddr));

        // marquage flags (resultat calculé dans la procédure Flags) 
        BINARY::fTaintCMP<len>(pTmgrTls, srcDest, src);	
        
        // déclaration de la contrainte s'il y avait un préfixe REP (codes 1 REPE = 0 et 2)
        if (repCode)  pFormula->addConstraint_ZERO(pTmgrTls, insAddress, (repCode == 1) ? true : false); 
    }
} // sCMPS