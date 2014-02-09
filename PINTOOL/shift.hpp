/*********/
/** SHL **/
/*********/

template<UINT32 len> 
void SHIFT::sSHL_IM(THREADID tid, UINT32 maskedDepl, ADDRINT writeAddr ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // opérande non marquée => démarquage flags
    if (!pTmgrGlobal->isMemoryTainted<len>(writeAddr)) pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le bit 0 de la source (si octet faible marqué) 
        if ((maskedDepl == len) && pTmgrGlobal->isMemoryTainted<8>(writeAddr))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_LSB,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddr))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrGlobal->unTaintMemory<len>(writeAddr);  // démarquage destination
    }
    // dans les autres cas : marquage par SHL
    else 
    {
        _LOGTAINT("SHLIM " << len << " ");
        ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<len>(writeAddr));

        // construction du résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHL,
            objSrcMem,
            ObjectSource(8, maskedDepl));

        // marquage flags
        fSHL(pTmgrTls, resultPtr, objSrcMem, maskedDepl);

        // MARQUAGE DESTINATION traitement par intervalle de déplacement
        // 1) détermination du nombre d'octets entiers déplacés
        UINT32 deplBytes = maskedDepl >> 3;
        // 2) cas des déplacements multiples de 8 bits (modulo 8 ou AND 7)
        if (!(maskedDepl & 0x7)) 
        {
            // 1ERE BOUCLE : octet fort marqué avec oct (fort - deplBytes) et ainsi de suite en décroissant les addresses
            // jusqu'à ce que adresse source = adresse de base (writeAddr)
            // pas de création d'objet, juste un déplacement
            ADDRINT toAddr   = writeAddr + (len >> 3) ; // octet fort +1 (1er octet de destination)
            ADDRINT fromAddr = toAddr - deplBytes;      // 1er octet de départ + 1
            while (fromAddr > writeAddr) 
            {
                // ajustement des adresses de départ et d'arrivée
                --fromAddr; --toAddr;
                // déplacement de l'octet "faible" (from) vers l'octet "fort" (to)
                if (pTmgrGlobal->isMemoryTainted<8>(fromAddr))
                {
                    pTmgrGlobal->updateMemoryTaint<8>(toAddr, pTmgrGlobal->getMemoryTaint<8>(fromAddr));
                }
                else pTmgrGlobal->unTaintMemory<8>(toAddr); 
            }
            
            // 2EME BOUCLE : demarquage des 'deplBytes' octets faibles
            for (ADDRINT lastAddr = writeAddr + deplBytes ; writeAddr < lastAddr ; ++writeAddr)
            {
                pTmgrGlobal->unTaintMemory<8>(writeAddr);
            }
        }
        // 3) cas général : marquage destination, puis demarquage octets faibles en fonction de l'intervalle de déplacement
        else 
        {  
            pTmgrGlobal->updateMemoryTaint<len>(writeAddr, resultPtr);
            for (ADDRINT lastAddr = writeAddr + deplBytes ; writeAddr < lastAddr ; ++writeAddr)
            {
                pTmgrGlobal->unTaintMemory<8>(writeAddr); 
            }
        }
    }
} // sSHL_IM

template<UINT32 len> 
void SHIFT::sSHL_IR(THREADID tid, UINT32 maskedDepl, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // opérande non marquée => démarquage flags
    if (!pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest 
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le bit 0 de la source (si octet faible marqué)
        REGINDEX regIndex = getRegIndex(reg);
        if ((maskedDepl == len) && pTmgrTls->isRegisterPartTainted(regIndex, 0))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_LSB,
                ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, 0))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrTls->unTaintRegister<len>(reg);  // démarquage destination
    }
    // dans les autres cas : marquage par SHL
    else 
    {
        _LOGTAINT("SHLIR " << len << " ");
        ObjectSource objSrcReg(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        REGINDEX regIndex = getRegIndex(reg);

        // construction du résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHL,
            objSrcReg,
            ObjectSource(8, maskedDepl));

        // marquage flags
        fSHL(pTmgrTls, resultPtr, objSrcReg, maskedDepl);

        // MARQUAGE DESTINATION traitement par intervalle de déplacement
        // 1) détermination du nombre d'octets entiers déplacés
        UINT32 deplBytes = maskedDepl >> 3;
        // 2) cas des déplacements multiples de 8 bits
        if (!(maskedDepl & 0x7)) 
        {
            // traitement par deux boucles while, avec comme index
            // de départ l'index haut, pour éviter les recoupements

            // 1ERE BOUCLE : octet fort marqué avec oct (fort - deplBytes) et ainsi de suite en décroissant les indexs
            // jusqu'à ce que index source = 0 ; pas de création d'objet, juste un déplacement
            for (UINT32 regPartFrom = (len >> 3) - deplBytes, regPartTo = (len >> 3) ; regPartFrom >= 0 ; --regPartFrom, --regPartTo)
            {
                // déplacement de l'octet "faible" (from) vers l'octet "fort" (to)
                if (pTmgrTls->isRegisterPartTainted(regIndex, regPartFrom))
                {
                    pTmgrTls->updateTaintRegisterPart(regIndex, regPartTo, 
                        pTmgrTls->getRegisterPartTaint(regIndex, regPartFrom));
                }
                else pTmgrTls->unTaintRegisterPart(regIndex, regPartTo);
            }

            // 2EME BOUCLE : demarquage indexs [0 ; deplBytes - 1]
            for (UINT32 regPart = 0 ; regPart < deplBytes ; ++regPart)
            {
                pTmgrTls->unTaintRegisterPart(regIndex, regPart);
            }
        }
        // 3) cas général : marquage destination, puis demarquage octets faibles en fonction de l'intervalle de déplacement
        else 
        {  
            pTmgrTls->updateTaintRegister<len>(reg, resultPtr);  
            for (UINT32 regPart = 0 ; regPart < deplBytes ; ++regPart)
            {
                pTmgrTls->unTaintRegisterPart(regIndex, regPart);
            }
        }
    }
} // sSHL_IR

template<UINT32 len> 
void SHIFT::sSHL_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    
    if ( !(isDestTainted || isCountTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SHL_IM
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SHL_IM
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHL_IM<len>(tid, maskDepl, writeAddress INSADDRESS); 
    }
    // forcément déplacement marqué
    else
    {
        _LOGTAINT("SHL_RM, déplacement marque, source " << ((isDestTainted) ? "marquee" : "non marquee"));
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        // création de l'objet correspondant à la mémoire shiftée
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));
       
        // création de l'objet resultat de l'opération
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHL,
            objSrcMem,
            objTbCount);    
            
        // marquage flags
        fSHL(pTmgrTls, resultPtr, objSrcMem, objTbCount);
        // marquage destination
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sSHL_RM

template<UINT32 len> 
void SHIFT::sSHL_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrTls->isRegisterTainted<len>(reg);
    
    if ( !(isDestTainted || isCountTainted) ) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais registre oui) => cas SHL_IR
    else if (!isCountTainted)
    {
        // masquage du déplacement avant appel de SHL_IR
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHL_IR<len>(tid, maskDepl, reg, regValue INSADDRESS); 
    }
    // forcément déplacement marqué
    else 
    {
        _LOGTAINT("SHL_RR, déplacement marque, source " << ((isDestTainted) ? "marquee" : "non marquee"));
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        // création de l'objet Source correspondant au registre shifté
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue))
            : ObjectSource(len, regValue);
        
        // création de l'objet resultat de l'opération
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHL,
            objSrcReg,
            objTbCount);    
            
        // marquage flags
        fSHL(pTmgrTls, resultPtr, objSrcReg, objTbCount);
        // marquage destination
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sSHL_RR

/*********/
/** SHR **/
/*********/

template<UINT32 len> 
void SHIFT::sSHR_IM(THREADID tid, UINT32 maskedDepl, ADDRINT writeAddr ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // opérande non marquée => démarquage flags
    if (!pTmgrGlobal->isMemoryTainted<len>(writeAddr)) pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le MSB de la source (si octet fort marqué)
        ADDRINT highAddress = writeAddr + (len >> 3) - 1;
        if ((maskedDepl == len) && pTmgrGlobal->isMemoryTainted<8>(highAddress))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_MSB,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(highAddress))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrGlobal->unTaintMemory<len>(writeAddr);  // démarquage destination 
    }
    else // dans les autres cas : marquage par SHR
    {
        _LOGTAINT("SHRIM " << len << " ");
        ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<len>(writeAddr));

        // construction du résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHR,
            objSrcMem,
            ObjectSource(8, maskedDepl));

        // marquage flags
        fSHR(pTmgrTls, resultPtr, objSrcMem, maskedDepl);

        // MARQUAGE DESTINATION traitement par intervalle de déplacement
        // 1) détermination du nombre d'octets entiers déplacés
        UINT32 deplBytes = maskedDepl >> 3;
        // 2) cas des déplacements multiples de 8 bits (modulo 8 ou AND 7)
        if (!(maskedDepl & 0x7))
        {
            // 1ERE BOUCLE : octet faible marqué avec oct (faible + deplBytes) et ainsi de suite en accroissant les addresses
            // jusqu'à ce que adresse source = adresse haute (writeAddr + (len>>3) - 1
            ADDRINT fromAddr = writeAddr + deplBytes - 1;   // 1er octet source (-1)
            ADDRINT toAddr   = writeAddr - 1;               // 1er octet de destination (-1)
            ADDRINT highAddress = writeAddr + (len >> 3);   // dernière adresse traitée = adresse haute exclue

            while (fromAddr < highAddress)
            {
                // ajustement des adresses de départ et d'arrivée
                ++fromAddr; ++toAddr;
                // déplacement de l'octet "fort" (from) vers l'octet "faible" (to)
                if (pTmgrGlobal->isMemoryTainted<8>(fromAddr))
                {
                    pTmgrGlobal->updateMemoryTaint<8>(toAddr, pTmgrGlobal->getMemoryTaint<8>(fromAddr));
                }
                else pTmgrGlobal->unTaintMemory<8>(toAddr);
            }

            // 2EME BOUCLE : demarquage des 'deplBytes' octets forts: [wA + (len >> 3) - deplBytes; wA + (len >> 3) [
            for (ADDRINT unTaintAddr = highAddress - deplBytes ; unTaintAddr < highAddress ; ++unTaintAddr)
            {
                pTmgrGlobal->unTaintMemory<8>(unTaintAddr);
            }
        }
        // 3) cas général : marquage destination, puis demarquage octets forts en fonction de l'intervalle de déplacement
        else 
        {           
            pTmgrGlobal->updateMemoryTaint<len>(writeAddr, resultPtr);
            ADDRINT highAddress = writeAddr + (len >> 3);   // dernière adresse traitée = adresse haute exclue
            for (ADDRINT unTaintAddr = highAddress - deplBytes ; unTaintAddr < highAddress ; ++unTaintAddr)
            {
                pTmgrGlobal->unTaintMemory<8>(unTaintAddr);
            }
        }
    }
} // sSHR_IM

template<UINT32 len> 
void SHIFT::sSHR_IR(THREADID tid, UINT32 maskedDepl, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // opérande non marquée => démarquage flags
    if (!pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest 
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
  
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le MSB de la source (si octet fort marqué)
        UINT32 highPart = (len >> 3) - 1;
        REGINDEX regIndex = getRegIndex(reg);
        if ((maskedDepl == len) && pTmgrTls->isRegisterPartTainted(regIndex, highPart))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_MSB,
                ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, highPart))));
        }
        else pTmgrTls->unTaintCarryFlag();
        
        pTmgrTls->unTaintRegister<len>(reg);  // démarquage destination
    }
    else // dans les autres cas : marquage par SHR
    {
        _LOGTAINT("SHRIR " << len << " ");
        ObjectSource objSrcReg(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        REGINDEX regIndex = getRegIndex(reg);

        // construction du résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHR,
            objSrcReg,
            ObjectSource(8, maskedDepl));

        // marquage flags
        fSHR(pTmgrTls, resultPtr, objSrcReg, maskedDepl);

        // MARQUAGE DESTINATION traitement par intervalle de déplacement
        // 1) détermination du nombre d'octets entiers déplacés
        UINT32 deplBytes = maskedDepl >> 3;
        // 2) cas des déplacements multiples de 8 bits
        if (!(maskedDepl & 0x7)) 
        {
            // 1ERE BOUCLE : octet faible marqué avec oct (faible + deplBytes) et ainsi de suite en accroissant les indexes
            // jusqu'à ce que index source = index fort (len>>3 - 1) ; pas de création d'objet, juste un déplacement
            UINT32 fromIndex = deplBytes;  // index source
            UINT32 toIndex = 0; // index de destination
                
            for (UINT32 regPartFrom = deplBytes, regPartTo = 0 ; regPartFrom < (len >> 3) ; ++regPartFrom, ++regPartTo) 
            {
                if (pTmgrTls->isRegisterPartTainted(regIndex, regPartFrom))
                {
                    pTmgrTls->updateTaintRegisterPart
                        (regIndex, regPartTo, pTmgrTls->getRegisterPartTaint(regIndex, regPartFrom));
                }
                else pTmgrTls->unTaintRegisterPart(regIndex, regPartTo);
            }

            // 2EME BOUCLE : demarquage des 'deplBytes' octets forts: [(len >> 3) - deplBytes; (len >> 3) [
            for (UINT32 regPart = (len >> 3) - deplBytes ; regPart < (len >> 3) ; ++regPart)
            {
                pTmgrTls->unTaintRegisterPart(regIndex, regPart);
            }
        }
        // 3) cas général : marquage destination, puis demarquage octets forts en fonction de l'intervalle de déplacement
        else 
        {
            pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
            for (UINT32 regPart = (len >> 3) - deplBytes ; regPart < (len >> 3) ; ++regPart)
            {
                pTmgrTls->unTaintRegisterPart(regIndex, regPart);
            }
        }
    }
} // sSHR_IR

template<UINT32 len> 
void SHIFT::sSHR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    
    if ( !(isDestTainted || isCountTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SHR_IM
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SHR_IM
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHR_IM<len>(tid, maskDepl, writeAddress INSADDRESS); 
    }
    // forcément déplacement marqué
    else
    {
        _LOGTAINT("SHR_RM, déplacement marque, source " << ((isDestTainted) ? "marquee" : "non marquee"));
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        // création de l'objet correspondant à la mémoire shiftée
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));

        // création de l'objet resultat de l'opération
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHR,
            objSrcMem,
            objTbCount);    
            
        // marquage flags
        fSHR(pTmgrTls, resultPtr, objSrcMem, objTbCount);
        // marquage destination
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sSHR_RM

template<UINT32 len> 
void SHIFT::sSHR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrTls->isRegisterTainted<len>(reg);
    
    if ( !(isDestTainted || isCountTainted) ) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais registre oui) => cas SHR_IR
    else if (!isCountTainted)
    {
        // masquage du déplacement avant appel de SHR_IR
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHR_IR<len>(tid, maskDepl, reg, regValue INSADDRESS); 
    }
    // forcément déplacement marqué
    else
    {
        _LOGTAINT("SHR_RR, déplacement marque, source " << ((isDestTainted) ? "marquee" : "non marquee"));
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        // création de l'objet Source correspondant au registre shifté
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue))
            : ObjectSource(len, regValue);
        
        // création de l'objet resultat de l'opération
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SHR,
            objSrcReg,
            objTbCount);    
            
        // marquage flags
        fSHR(pTmgrTls, resultPtr, objSrcReg, objTbCount);
        // marquage destination
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sSHR_RR

/*********/
/** SAR **/
/*********/

template<UINT32 len> 
void SHIFT::sSAR_IM(THREADID tid, UINT32 maskedDepl, ADDRINT writeAddr ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // opérande non marquée => démarquage flags
    if (!pTmgrGlobal->isMemoryTainted<len>(writeAddr)) pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le MSB de la source (si octet fort marqué)
        ADDRINT highAddress = writeAddr + (len >> 3) - 1;
        if ((maskedDepl == len) && pTmgrGlobal->isMemoryTainted<8>(highAddress))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_MSB,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(highAddress))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrGlobal->unTaintMemory<len>(writeAddr);  // démarquage destination 
    }
    else // dans les autres cas : marquage par SAR
    {
        _LOGTAINT("SARIM " << len << " ");
        ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<len>(writeAddr));

        // construction du résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SAR,
            objSrcMem,
            ObjectSource(8, maskedDepl));

        // marquage flags
        fSAR(pTmgrTls, resultPtr, objSrcMem, maskedDepl);

        // MARQUAGE DESTINATION 
        pTmgrGlobal->updateMemoryTaint<len>(writeAddr, resultPtr);
    }
} // sSAR_IM

template<UINT32 len> 
void SHIFT::sSAR_IR(THREADID tid, UINT32 maskedDepl, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{  
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // opérande non marquée => démarquage flags
    if (!pTmgrTls->isRegisterTainted<len>(reg)) pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest 
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
  
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le MSB de la source (si octet fort marqué)
        UINT32 highPart = (len >> 3) - 1;
        REGINDEX regIndex = getRegIndex(reg);
        if ((maskedDepl == len) && pTmgrTls->isRegisterPartTainted(regIndex, highPart))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_MSB,
                ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, highPart))));
        }
        else pTmgrTls->unTaintCarryFlag();
        
        pTmgrTls->unTaintRegister<len>(reg);  // démarquage destination
    }
    else // dans les autres cas : marquage par SAR
    {
        _LOGTAINT("SARIR " << len << " ");
        ObjectSource objSrcReg(pTmgrTls->getRegisterTaint<len>(reg, regValue));
        REGINDEX regIndex = getRegIndex(reg);

        // construction du résultat
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SAR,
            objSrcReg,
            ObjectSource(8, maskedDepl));

        // marquage flags
        fSAR(pTmgrTls, resultPtr, objSrcReg, maskedDepl);

        // MARQUAGE DESTINATION 
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sSAR_IR

template<UINT32 len> 
void SHIFT::sSAR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    
    if ( !(isDestTainted || isCountTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SAR_IM
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SAR_IM
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSAR_IM<len>(tid, maskDepl, writeAddress INSADDRESS); 
    }
    // forcément déplacement marqué
    else
    {
        _LOGTAINT("SAR_RM, déplacement marque, source " << ((isDestTainted) ? "marquee" : "non marquee"));
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        // création de l'objet correspondant à la mémoire shiftée
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));

        // création de l'objet resultat de l'opération
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SAR,
            objSrcMem,
            objTbCount);    
            
        // marquage flags
        fSAR(pTmgrTls, resultPtr, objSrcMem, objTbCount);
        // marquage destination
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sSAR_RM

template<UINT32 len> 
void SHIFT::sSAR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrTls->isRegisterTainted<len>(reg);
    
    if ( !(isDestTainted || isCountTainted) ) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais registre oui) => cas SAR_IR
    else if (!isCountTainted)
    {
        // masquage du déplacement avant appel de SAR_IR
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSAR_IR<len>(tid, maskDepl, reg, regValue INSADDRESS); 
    }
    // forcément déplacement marqué
    else
    {
        _LOGTAINT("SAR_RR, déplacement marque, source " << ((isDestTainted) ? "marquee" : "non marquee"));
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        // création de l'objet Source correspondant au registre shifté
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(reg, regValue))
            : ObjectSource(len, regValue);
        
        // création de l'objet resultat de l'opération
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            X_SAR,
            objSrcReg,
            objTbCount);    
            
        // marquage flags
        fSAR(pTmgrTls, resultPtr, objSrcReg, objTbCount);
        // marquage destination
        pTmgrTls->updateTaintRegister<len>(reg, resultPtr);
    }
} // sSAR_RR

/**********/
/** SHLD **/
/**********/

// TODO : tester le marquage octet par octet du 'bit pattern' (seconde opérande)
// afin d'affiner le démarquage éventuel de la destination. Valable surtout pour le marquage bit par bit

template<UINT32 len> void SHIFT::sSHLD_IM
    (THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddr ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddr);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    // opérandes non marquées => démarquage flags
    if (!(isSrcDestTainted || isRegSrcTainted))  pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le bit 0 de la source (si octet faible marqué) 
        if ((maskedDepl == len) && pTmgrGlobal->isMemoryTainted<8>(writeAddr))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_LSB,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(writeAddr))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrGlobal->unTaintMemory<len>(writeAddr);  // démarquage destination
    }
    // dans les autres cas : marquage par SHL
    else 
    {
        _LOGTAINT("SHLDIM " << len << " ");

        ObjectSource objMemSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddr))
            : ObjectSource(len, getMemoryValue<len>(writeAddr));
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(CONCAT, objMemSrcDest, objRegSrc);

        // déplacement avec SHL sur (len*2) bits
        TaintObject<(2*len)> shiftOperation(X_SHL,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc)),
            ObjectSource(8, maskedDepl));

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags; SEUL la source originale (ici mémoire) est utilisée pour le marquage des flags
        // cf implémentation de fSHL (le 'bit pattern' est inutile)
        fSHLD(pTmgrTls, resultPtr, objMemSrcDest, maskedDepl);

        // MARQUAGE DESTINATION
        pTmgrGlobal->updateMemoryTaint<len>(writeAddr, resultPtr);
    }
} // sSHLD_IM

template<UINT32 len> void SHIFT::sSHLD_IR
    (THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    // opérandes non marquées => démarquage flags
    if (!(isSrcDestTainted || isRegSrcTainted))  pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest 
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le bit 0 de la source (si octet faible marqué)
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        if ((maskedDepl == len) && pTmgrTls->isRegisterPartTainted(regSrcDestIndex, 0))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_LSB,
                ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, 0))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrTls->unTaintRegister<len>(regSrcDest);  // démarquage destination
    }
    // dans les autres cas : marquage par SHL
    else
    {
        _LOGTAINT("SHLD_IR " << len << " ");
               
        ObjectSource objRegSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(CONCAT, objRegSrcDest, objRegSrc);

        // déplacement avec SHL sur (len*2) bits
        TaintObject<(2*len)> shiftOperation(X_SHL,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc)),
            ObjectSource(8, maskedDepl));

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags; SEUL la source originale (ici registre srcDest) est utilisée pour le marquage des flags
        // cf implémentation de fSHL (le 'bit pattern' est inutile)
        fSHLD(pTmgrTls, resultPtr, objRegSrcDest, maskedDepl);

        // MARQUAGE DESTINATION
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);
    }
} // sSHLD_IR

template<UINT32 len> void SHIFT::sSHLD_RM
    (THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted   = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    if ( !(isCountTainted || isSrcDestTainted || isRegSrcTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SHLD_IM
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SHLD_IM
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHLD_IM<len>(tid, maskDepl, regSrc, regSrcValue, writeAddress INSADDRESS); 
    }
    else // déplacement marqué. Mémoire et Bit Pattern marqués ou non  
    {
        _LOGTAINT("SHLD_RM " << len << " ");
        
        ObjectSource objMemSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);

        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(CONCAT, objMemSrcDest, objRegSrc);
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));

        // déplacement avec SHL sur (len*2) bits, déplacement marqué
        TaintObject<(2*len)> shiftOperation(X_SHL,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc)),
            objTbCount);

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags; SEUL la source originale (ici mémoire) est utilisée pour le marquage des flags
        // cf implémentation de fSHL (le 'bit pattern' est inutile)
        fSHLD(pTmgrTls, resultPtr, objMemSrcDest, objTbCount);

        // MARQUAGE DESTINATION
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sSHLD_RM

template<UINT32 len> void SHIFT::sSHLD_RR
    (THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted   = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    if ( !(isCountTainted || isSrcDestTainted || isRegSrcTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SHLD_IR
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SHLD_IR
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHLD_IR<len>(tid, maskDepl, regSrc, regSrcValue, regSrcDest, regSrcDestValue INSADDRESS); 
    }
    else // déplacement marqué ; Registre et Bit Pattern marqués ou non  
    {
        _LOGTAINT("SHLD_RR " << len << " ");
        
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));

        ObjectSource objRegSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(CONCAT, objRegSrcDest, objRegSrc);

        // déplacement avec SHL sur (len*2) bits, déplacement marqué
        TaintObject<(2*len)> shiftOperation(X_SHL,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc)),
            objTbCount);

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags; SEUL la source originale (ici registre srcDest) est utilisée pour le marquage des flags
        // cf implémentation de fSHL (le 'bit pattern' est inutile)
        fSHLD(pTmgrTls, resultPtr, objRegSrcDest, objTbCount);

        // MARQUAGE DESTINATION
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);
    }
} // sSHLD_RR
 
/**********/
/** SHRD **/
/**********/

template<UINT32 len> void SHIFT::sSHRD_IM
    (THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddr ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddr);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    // opérandes non marquées => démarquage flags
    if (!(isSrcDestTainted || isRegSrcTainted))  pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le MSB de la source (si octet fort marque)
        ADDRINT highAddress = writeAddr + (len >> 3) - 1;
        if ((maskedDepl == len) && pTmgrGlobal->isMemoryTainted<8>(highAddress))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_MSB,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(highAddress))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrGlobal->unTaintMemory<len>(writeAddr);  // démarquage destination 
    }
    else // dans les autres cas : marquage par SHR
    {
        _LOGTAINT("SHRD_IM " << len << " ");
            
        ObjectSource objMemSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddr))
            : ObjectSource(len, getMemoryValue<len>(writeAddr));
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(
            CONCAT, 
            objMemSrcDest, 
            objRegSrc);
        ObjectSource objConcatenatedSrc(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc));

        // déplacement avec SHR sur (len*2) bits
        TaintObject<(2*len)> shiftOperation(X_SHR,
            objConcatenatedSrc,
            ObjectSource(8, maskedDepl));

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte

        // marquage flags
        fSHRD(pTmgrTls, resultPtr, objConcatenatedSrc, maskedDepl);

        // MARQUAGE DESTINATION
        pTmgrGlobal->updateMemoryTaint<len>(writeAddr, resultPtr);
    }
} // sSHRD_IM

template<UINT32 len> void SHIFT::sSHRD_IR
    (THREADID tid, UINT32 maskedDepl, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);

    // opérandes non marquées => démarquage flags
    if (!(isSrcDestTainted || isRegSrcTainted))  pTmgrTls->unTaintAllFlags();
    // déplacement >= taille destination => démarquage flags et dest 
    else if (maskedDepl >= len) 
    {  
        fUnTaintOZSAP(pTmgrTls); // démarquage OZASP
            
        // marquage CF si dplt = à la taille de la destination
        // dans ce cas, le carryFlag contiendra le bit 0 de la source (si octet faible marqué)
        REGINDEX regSrcDestIndex = getRegIndex(regSrcDest);
        if ((maskedDepl == len) && pTmgrTls->isRegisterPartTainted(regSrcDestIndex, 0))
        {
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_LSB,
                ObjectSource(pTmgrTls->getRegisterPartTaint(regSrcDestIndex, 0))));
        }
        else pTmgrTls->unTaintCarryFlag();

        pTmgrTls->unTaintRegister<len>(regSrcDest);  // démarquage destination
    }
    else // dans les autres cas : marquage par SHR
    {
        _LOGTAINT("SHRD_IR " << len << " ");
            
        ObjectSource objRegSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(
            CONCAT, 
            objRegSrcDest, 
            objRegSrc);
        ObjectSource objConcatenatedSrc(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc));

        // déplacement avec SHL sur (len*2) bits
        TaintObject<(2*len)> shiftOperation(X_SHR,
            objConcatenatedSrc,
            ObjectSource(8, maskedDepl));

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags
        fSHRD(pTmgrTls, resultPtr, objConcatenatedSrc, maskedDepl);

        // MARQUAGE DESTINATION
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);
    }
} // sSHRD_IR

template<UINT32 len> void SHIFT::sSHRD_RM
    (THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, ADDRINT writeAddress ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted   = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isSrcDestTainted = pTmgrGlobal->isMemoryTainted<len>(writeAddress);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    if ( !(isCountTainted || isSrcDestTainted || isRegSrcTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SHRD_IM
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SHRD_IM
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHRD_IM<len>(tid, maskDepl, regSrc, regSrcValue, writeAddress INSADDRESS); 
    }
    else // déplacement marqué. Mémoire et Bit Pattern marqués ou non  
    {
        _LOGTAINT("SHRD_RM " << len << " ");
        
        ObjectSource objMemSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<len>(writeAddress))
            : ObjectSource(len, getMemoryValue<len>(writeAddress));
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);

        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(
            CONCAT, 
            objMemSrcDest, 
            objRegSrc);
        ObjectSource objConcatenatedSrc(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc));
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));

        // déplacement avec SHR sur (len*2) bits, déplacement marqué
        TaintObject<(2*len)> shiftOperation(X_SHR,
            objConcatenatedSrc,
            objTbCount);

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags
        fSHRD(pTmgrTls, resultPtr, objConcatenatedSrc, objTbCount);

        // MARQUAGE DESTINATION
        pTmgrGlobal->updateMemoryTaint<len>(writeAddress, resultPtr);
    }
} // sSHRD_RM

template<UINT32 len> void SHIFT::sSHRD_RR
    (THREADID tid, ADDRINT regCLValue, REG regSrc, ADDRINT regSrcValue, REG regSrcDest, ADDRINT regSrcDestValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    bool isCountTainted   = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isSrcDestTainted = pTmgrTls->isRegisterTainted<len>(regSrcDest);
    bool isRegSrcTainted  = pTmgrTls->isRegisterTainted<len>(regSrc);
    
    if ( !(isCountTainted || isSrcDestTainted || isRegSrcTainted)) pTmgrTls->unTaintAllFlags();
    // déplacement non marqué (mais mémoire oui) => cas SHRD_IR
    else if (!isCountTainted) 
    {
        // masquage du déplacement avant appel de SHRD_IR
        UINT32 maskDepl = (len == 64) ? (regCLValue & 0x3f) : (regCLValue & 0x1f);
        sSHRD_IR<len>(tid, maskDepl, regSrc, regSrcValue, regSrcDest, regSrcDestValue INSADDRESS); 
    }
    else // déplacement marqué ; Registre et Bit Pattern marqués ou non  
    {
        _LOGTAINT("SHRD_RR " << len << " ");

        ObjectSource objRegSrcDest = (isSrcDestTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrcDest, regSrcDestValue))
            : ObjectSource(len, regSrcDestValue);
        ObjectSource objRegSrc = (isRegSrcTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(regSrc, regSrcValue))
            : ObjectSource(len, regSrcValue);
        
        // concaténation de la source et du bit pattern
        TaintObject<(2*len)> concatenatedSrc(
            CONCAT, 
            objRegSrcDest, 
            objRegSrc);
        ObjectSource objConcatenatedSrc(std::make_shared<TaintObject<(2*len)>>(concatenatedSrc));
        // récupération du déplacement marqué
        ObjectSource objTbCount(pTmgrTls->getRegisterTaint(REG_CL));
        
        // déplacement avec SHR sur (len*2) bits, déplacement marqué
        TaintObject<(2*len)> shiftOperation(X_SHR,
            objConcatenatedSrc,
            objTbCount);

        // construction du résultat : extraction de la partie forte de shiftOperation
        std::shared_ptr<TaintObject<len>> resultPtr = std::make_shared<TaintObject<len>>(
            EXTRACT,
            ObjectSource(std::make_shared<TaintObject<(2*len)>>(shiftOperation)),
            ObjectSource(8, 1)); // extract de longueur 'len' : 0 = partie faible, 1 = partie forte 

        // marquage flags
        fSHRD(pTmgrTls, resultPtr, objConcatenatedSrc, objTbCount);

        // MARQUAGE DESTINATION
        pTmgrTls->updateTaintRegister<len>(regSrcDest, resultPtr);
    }
} // sSHRD_RR
 