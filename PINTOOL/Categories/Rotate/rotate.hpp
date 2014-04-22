/*********/
/** ROL **/
/*********/

template<UINT32 lengthInBits> 
void ROTATE::sROL_IM(THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT insAddress) 
{  
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // opérande non marquée => démarquage flags
    if (!pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // masque pour le déplacement
        UINT32 countMask = (lengthInBits == 64) ? 0x3f : 0x1f;
        /* ROL instruction operation *)
        tempCOUNT ← (COUNT & COUNTMASK) MOD SIZE */
        UINT32 tempDepl  = (depl & countMask) % lengthInBits;
        
        _LOGTAINT(tid, insAddress, "ROLIM " + decstr(lengthInBits));
        
        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROL,
            ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)),  
            ObjectSource(8, tempDepl));

        // marquage flags
        ObjectSource objResult(resultPtr);
        // CF/ROL = recopie du dernier bit éjecté à gauche, qui est en fait le LSB du résultat
        TaintBitPtr cfPtr = std::make_shared<TaintBit>(F_LSB, objResult);
        pTmgrTls->updateTaintCarryFlag(cfPtr);  
        // OF/ROL : ssi (depl & countMask) = 1 (sans modulo), sinon démarquage
        if ((depl & countMask) == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
                F_OVERFLOW_ROL, objResult, ObjectSource(cfPtr)));
        }
        else pTmgrTls->unTaintOverflowFlag();

        // MARQUAGE DESTINATION 
        // 1) cas des déplacements multiples de 8 bits : simple déplacement du marquage
        // cela évite la multiplication des objets marqués
        if ((tempDepl & 0x7) == 0) 
        {
            // sauvegarde du marquage de la source dans un vecteur
            vector<TaintBytePtr> vSavedSrc;
            ADDRINT highestAddress = writeAddress + (lengthInBits >> 3);
            for (ADDRINT targetAddress = writeAddress ; targetAddress < highestAddress ; ++targetAddress)
            {
                // objet ou nullptr selon le marquage
                vSavedSrc.push_back(pTmgrGlobal->getMemoryTaint<8>(targetAddress));
            }

            // itérateurs de début et de fin du vecteur représentant la source
            vector<TaintBytePtr>::iterator it     = vSavedSrc.begin();
            vector<TaintBytePtr>::iterator lastIt = vSavedSrc.end();

            // parcours de chaque octet de la source, et affectation à l'octet de destination
            // pour ROL, l'octet 0 va se retrouver à l'octet d'offset 'maskedDepl >> 3'
            // et ainsi de suite. Si la destination dépasse l'adresse haute, la destination est l'offset 0
            for (ADDRINT targetAddress = writeAddress + (tempDepl >> 3) ; it != lastIt ; ++it, ++targetAddress)
            {
                // Si arrivé à l'octet fort => repartir à l'offset 0
                if (targetAddress == highestAddress) targetAddress = writeAddress;
                
                // réaffectation de l'octet source à la bonne place apres rotation
                if ((bool) *it) pTmgrGlobal->updateMemoryTaint<8>(targetAddress, *it);
                else            pTmgrGlobal->unTaintMemory<8>(targetAddress);
            }        
        }
        // 2) autre cas : marquage destination 'normalement'
        else  pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sROL_IM

template<UINT32 lengthInBits> 
void ROTATE::sROL_IR(THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT insAddress) 
{  
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // opérande non marquée => démarquage flags
    if (!pTmgrTls->isRegisterTainted<lengthInBits>(reg)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // masque pour le déplacement
        UINT32 countMask = (lengthInBits == 64) ? 0x3f : 0x1f;
        /* ROL instruction operation *)
        tempCOUNT ← (COUNT & COUNTMASK) MOD SIZE */
        UINT32 tempDepl  = (depl & countMask) % lengthInBits;

        _LOGTAINT(tid, insAddress, "ROLIR " + decstr(lengthInBits));
        
        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROL,
            ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue)),  
            ObjectSource(8, depl));

        // marquage flags
        ObjectSource objResult(resultPtr);
        // CF/ROL = recopie du dernier bit éjecté à gauche, qui est en fait le LSB du résultat
        TaintBitPtr cfPtr = std::make_shared<TaintBit>(F_LSB, objResult);
        pTmgrTls->updateTaintCarryFlag(cfPtr);  
        // OF/ROL : ssi (depl & countMask) = 1 (sans modulo), sinon démarquage
        if ((depl & countMask) == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
                F_OVERFLOW_ROL, objResult, ObjectSource(cfPtr)));
        }
        else pTmgrTls->unTaintOverflowFlag();

        // MARQUAGE DESTINATION 
        // 1) cas des déplacements multiples de 8 bits : simple déplacement du marquage
        // cela évite la multiplication des objets marqués
        if ((tempDepl & 0x7) == 0) 
        {
            // sauvegarde du marquage de la source dans un vecteur
            REGINDEX regIndex = getRegIndex(reg);
            vector<TaintBytePtr> vSavedSrc;
            for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart)
            {
                // objet ou nullptr selon le marquage
                vSavedSrc.push_back(pTmgrTls->getRegisterPartTaint(regIndex, regPart));
            }

            // itérateurs de début et de fin du vecteur représentant la source
            auto it = vSavedSrc.begin(), lastIt = vSavedSrc.end();
            
            // parcours de chaque octet de la source, et affectation à l'octet de destination
            // pour ROL, l'octet 0 va se retrouver à l'octet 'maskedDepl >> 3'
            // et ainsi de suite. Si la destination dépasse l'index haut, la destination est l'octet 0
            for (UINT32 regPart = tempDepl >> 3 ; it != lastIt ; ++it, ++regPart)
            {
                // Si arrivé à l'octet fort => repartir à l'offset 0
                if (regPart == lengthInBits >> 3) regPart = 0;

                if ((bool) *it) pTmgrTls->updateTaintRegisterPart(regIndex, regPart, *it);
                else pTmgrTls->unTaintRegisterPart(regIndex, regPart);
            }
        }
        // 2) autre cas : marquage destination 'normalement'
        else  pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sROL_IR

template<UINT32 lengthInBits> 
void ROTATE::sROL_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);
    
    if ( !(isDestTainted || isCountTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais mémoire oui) => cas ROL_IM
    else if (!isCountTainted) sROL_IM<lengthInBits>(tid, (UINT32) regCLValue, writeAddress ,insAddress); 
    else // déplacement marqué  
    {
        _LOGTAINT(tid, insAddress, "ROL_RM" + decstr(lengthInBits));
            
        // création de l'objet Source correspondant à la mémoire
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)) 
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress)); 

        // création de l'objet resultat de l'opération
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROL,
            objSrcMem,
            ObjectSource(pTmgrTls->getRegisterTaint(REG_CL))); // CL contient le nombre de bits de la rotation

        // marquage flags 
        // CF/ROL = recopie du dernier bit éjecté à gauche, qui est en fait le LSB du résultat
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_LSB, ObjectSource(resultPtr)));
        // OF/ROL : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sROL_RM

template<UINT32 lengthInBits> 
void ROTATE::sROL_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(reg);
    
    if ( !(isDestTainted || isCountTainted) )
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais registre oui) => cas ROL_IR
    else if (!isCountTainted) sROL_IR<lengthInBits>(tid, (UINT32) regCLValue, reg, regValue ,insAddress); 
    else // déplacement marqué 
    {
        _LOGTAINT(tid, insAddress, "ROL_RR" + decstr(lengthInBits));
        
        // création de l'objet Source correspondant au registre cible
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue))
            : ObjectSource(lengthInBits, regValue); 

        // création de l'objet resultat de l'opération
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROL,
            objSrcReg,
            ObjectSource(pTmgrTls->getRegisterTaint(REG_CL))); // CL contient le nombre de bits de la rotation

        // marquage flags 
        // CF/ROL = recopie du dernier bit éjecté à gauche, qui est en fait le LSB du résultat
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_LSB, ObjectSource(resultPtr)));
        // OF/ROL : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sROL_RR


/*********/
/** ROR **/
/*********/

template<UINT32 lengthInBits> 
void ROTATE::sROR_IM(THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // opérande non marquée => démarquage flags
    if (!pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // masque pour le déplacement
        UINT32 countMask = (lengthInBits == 64) ? 0x3f : 0x1f;
        /* ROR instruction operation *)
        tempCOUNT ← (COUNT & COUNTMASK) MOD SIZE */
        UINT32 tempDepl  = (depl & countMask) % lengthInBits;
        
        _LOGTAINT(tid, insAddress, "RORIM " + decstr(lengthInBits));
        
        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROR,
            ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)),  
            ObjectSource(8, tempDepl));

        // marquage flags
        ObjectSource objResult(resultPtr);
        // CF/ROR = recopie du dernier bit éjecté à droite, qui est en fait le MSB du résultat
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_MSB, objResult));   
        // OF/ROR : ssi depl ORIGINAL vaut 1, sinon démarquage
        if ((depl & countMask) == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_ROR, objResult));
        }
        else pTmgrTls->unTaintOverflowFlag();

        // MARQUAGE DESTINATION 
        // 1) cas des déplacements multiples de 8 bits : simple déplacement du marquage
        // cela évite la multiplication des objets marqués
        if ((tempDepl & 0x7) == 0) 
        {
            // sauvegarde du marquage de la source dans un vecteur
            vector<TaintBytePtr> vSavedSrc;
            ADDRINT highestAddress = writeAddress + (lengthInBits >> 3);
            for (ADDRINT targetAddress = writeAddress ; targetAddress < highestAddress ; ++targetAddress)
            {
                // objet ou nullptr selon le marquage
                vSavedSrc.push_back(pTmgrGlobal->getMemoryTaint<8>(targetAddress));
            }

            // itérateurs de début et de fin du vecteur représentant la source
            auto it = vSavedSrc.begin(), lastIt = vSavedSrc.end();

            // parcours de chaque octet de la source, et affectation à l'octet de destination
            // pour ROR, l'octet 0 va se retrouver à l'octet d'offset '(lengthInBits >> 3) - (maskedDepl >> 3)'
            // et ainsi de suite. Si la destination dépasse l'adresse haute, la destination est l'offset 0
            for (ADDRINT targetAddress = writeAddress + (lengthInBits >> 3) - (tempDepl >> 3) ; it != lastIt ; ++it, ++targetAddress)
            {
                // Si arrivé à l'octet fort => repartir à l'offset 0
                if (targetAddress == highestAddress) targetAddress = writeAddress;
                
                // réaffectation de l'octet source à la bonne place apres rotation
                if ((bool) *it) pTmgrGlobal->updateMemoryTaint<8>(targetAddress, *it);
                else            pTmgrGlobal->unTaintMemory<8>(targetAddress);
            }        
        }
        // 2) autre cas : marquage destination 'normalement'
        else  pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
}   

template<UINT32 lengthInBits> 
void ROTATE::sROR_IR(THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // opérande non marquée => démarquage flags
    if (!pTmgrTls->isRegisterTainted<lengthInBits>(reg)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // masque pour le déplacement
        UINT32 countMask = (lengthInBits == 64) ? 0x3f : 0x1f;
        /* ROR instruction operation *)
        tempCOUNT ← (COUNT & COUNTMASK) MOD SIZE */
        UINT32 tempDepl  = (depl & countMask) % lengthInBits;

        _LOGTAINT(tid, insAddress, "ROLIR " + decstr(lengthInBits));
        
        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROR,
            ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue)),  
            ObjectSource(8, tempDepl));

        // marquage flags
        ObjectSource objResult(resultPtr);
        // CF/ROR = recopie du dernier bit éjecté à droite, qui est en fait le MSB du résultat
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_MSB, objResult));   
        // OF/ROR : ssi depl ORIGINAL vaut 1, sinon démarquage
        if ((depl & countMask) == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(F_OVERFLOW_ROR, objResult));
        }
        else pTmgrTls->unTaintOverflowFlag();

        // MARQUAGE DESTINATION 
        // 1) cas des déplacements multiples de 8 bits : simple déplacement du marquage
        // cela évite la multiplication des objets marqués
        if ((tempDepl & 0x7) == 0) 
        {
            // sauvegarde du marquage de la source dans un vecteur
            REGINDEX regIndex = getRegIndex(reg);
            vector<TaintBytePtr> vSavedSrc;
            for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart)
            {
                // objet ou nullptr selon le marquage
                vSavedSrc.push_back(pTmgrTls->getRegisterPartTaint(regIndex, regPart));
            }

            // itérateurs de début et de fin du vecteur représentant la source
            auto it = vSavedSrc.begin(), lastIt = vSavedSrc.end();

            // parcours de chaque octet de la source, et affectation à l'octet de destination
            // pour ROR, l'octet 0 va se retrouver à l'octet 'lengthInBits >> 3' - 'maskedDepl >> 3'
            // et ainsi de suite. Si la destination dépasse l'index haut, la destination est l'octet 0
            for (UINT32 regPart = (lengthInBits >> 3) - (tempDepl >> 3) ; it != lastIt ; ++it, ++regPart)
            {
                // Si arrivé à l'octet fort => repartir à l'offset 0
                if (regPart == lengthInBits >> 3) regPart = 0;

                if ((bool) *it) pTmgrTls->updateTaintRegisterPart(regIndex, regPart, *it);
                else pTmgrTls->unTaintRegisterPart(regIndex, regPart);
            }
        }
        // 2) autre cas : marquage destination 'normalement'
        else  pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sROR_IR

template<UINT32 lengthInBits> 
void ROTATE::sROR_RM(THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);
    
    if ( !(isDestTainted || isCountTainted)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais mémoire oui) => cas ROR_IM
    else if (!isCountTainted)  sROR_IM<lengthInBits>(tid, (UINT32) regCLValue, writeAddress ,insAddress);
    else // déplacement marqué  
    {
        _LOGTAINT(tid, insAddress, "ROR_RM" + decstr(lengthInBits));
            
        // création de l'objet Source correspondant à la mémoire
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)) 
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress)); 

        // création de l'objet resultat de l'opération
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROR,
            objSrcMem,
            ObjectSource(pTmgrTls->getRegisterTaint(REG_CL))); // CL contient le nombre de bits de la rotation

        // marquage flags 
        // CF/ROR = recopie du dernier bit éjecté à droite, qui est en fait le MSB du résultat
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_MSB, ObjectSource(resultPtr)));
        // OF/ROR : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sROR_RM

template<UINT32 lengthInBits>
void ROTATE::sROR_RR(THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(reg);
    
    if ( !(isDestTainted || isCountTainted) )
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais registre oui) => cas ROR_IR
    else if (!isCountTainted) sROR_IR<lengthInBits>(tid, (UINT32) regCLValue, reg, regValue ,insAddress);  
    else // déplacement marqué 
    {
        _LOGTAINT(tid, insAddress, "ROR_RR" + decstr(lengthInBits));
        
        // création de l'objet Source correspondant au registre cible
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue))
            : ObjectSource(lengthInBits, regValue); 

        // création de l'objet resultat de l'opération
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_ROR,
            objSrcReg,
            ObjectSource(pTmgrTls->getRegisterTaint(REG_CL))); // CL contient le nombre de bits de la rotation

        // marquage flags 
        ObjectSource objResult(resultPtr);
        // CF/ROR = recopie du dernier bit éjecté à droite, qui est en fait le MSB du résultat
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_MSB, objResult));   
        // OF/ROR : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sROR_RR

/*********/
/** RCL **/
/*********/

template<UINT32 lengthInBits> void ROTATE::sRCL_IM
    (THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress)
{  
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isSrcTainted       = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();

    // opérandes non marquées => démarquage flags 
    if (!(isSrcTainted || isCarryFlagTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // MANUEL INTEL : 
        /* CASE (determine count) OF
        SIZE ← 8: tempCOUNT ← (COUNT AND 1FH) MOD 9;
        SIZE ← 16: tempCOUNT ← (COUNT AND 1FH) MOD 17;
        SIZE ← 32: tempCOUNT ← COUNT AND 1FH;
        SIZE ← 64: tempCOUNT ← COUNT AND 3FH;
        ESAC; */
        UINT32 tempDepl = 0;
        switch (lengthInBits)
        {
        case 8:  tempDepl = (depl & 0x1f) % 9;  break;
        case 16: tempDepl = (depl & 0x1f) % 17; break;
        case 32: tempDepl = (depl & 0x1f); break;
        case 64: tempDepl = (depl & 0x3f); break;
        }

        _LOGTAINT(tid, insAddress, "RCL_IM " + decstr(lengthInBits));

        // Récupération du marquage ou valeur de la mémoire
        ObjectSource objSrcMem = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_RCL,
            objSrcMem,
            objSrcCF,
            ObjectSource(8, tempDepl));

        // marquage flags
        // CF/RCL : recopie du dernier bit de la source ejecté à gauche 
        // c'est à dire bit 'lengthInBits - depl' de la source
        UINT32 bitNumber    = lengthInBits - tempDepl;
        TaintBitPtr cfPtr   = std::make_shared<TaintBit>(EXTRACT, objSrcMem, ObjectSource(8, bitNumber));
        pTmgrTls->updateTaintCarryFlag(cfPtr);
        // OF/RCL ssi deplacement ORIGINAL vaut 1 
        if (depl == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
                F_OVERFLOW_ROL, // RCL : calcul identique à ROL
                ObjectSource(resultPtr),
                ObjectSource(cfPtr))); // CF apres la rotation, tout juste calculé
        }
        else pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sRCL_IM

template<UINT32 lengthInBits> void ROTATE::sRCL_IR
    (THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT regGflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isSrcTainted       = pTmgrTls->isRegisterTainted<lengthInBits>(reg);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();
    
    // opérandes non marquées => démarquage flags 
    if (!(isSrcTainted || isCarryFlagTainted)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // MANUEL INTEL : 
        /* CASE (determine count) OF
        SIZE ← 8: tempCOUNT ← (COUNT AND 1FH) MOD 9;
        SIZE ← 16: tempCOUNT ← (COUNT AND 1FH) MOD 17;
        SIZE ← 32: tempCOUNT ← COUNT AND 1FH;
        SIZE ← 64: tempCOUNT ← COUNT AND 3FH;
        ESAC; */
        UINT32 tempDepl = 0;
        switch (lengthInBits)
        {
        case 8:  tempDepl = (depl & 0x1f) % 9;  break;
        case 16: tempDepl = (depl & 0x1f) % 17; break;
        case 32: tempDepl = (depl & 0x1f); break;
        case 64: tempDepl = (depl & 0x3f); break;
        }
   
        _LOGTAINT(tid, insAddress, "RCL_IR " + decstr(lengthInBits));
        
        // Récupération du marquage ou valeur du registre
        ObjectSource objSrcReg = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue))
            : ObjectSource(lengthInBits, regValue);
        
        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_RCL,
            objSrcReg,
            objSrcCF,
            ObjectSource(8, tempDepl));

        // marquage flags
        // CF/RCL : recopie du dernier bit de la source ejecté à gauche 
        // c'est à dire bit 'lengthInBits - depl' de la source
        UINT32 bitNumber    = lengthInBits - tempDepl;
        TaintBitPtr cfPtr   = std::make_shared<TaintBit>(EXTRACT, objSrcReg, ObjectSource(8, bitNumber));
        pTmgrTls->updateTaintCarryFlag(cfPtr);
        // OF/RCL ssi deplacement ORIGINAL vaut 1 
        if (depl == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
                F_OVERFLOW_ROL, // RCL : calcul identique à ROL
                ObjectSource(resultPtr),
                ObjectSource(cfPtr))); // CF apres la rotation, tout juste calculé
        }
        else pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sRCL_IR

template<UINT32 lengthInBits> void ROTATE::sRCL_RM
    (THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted     = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted      = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();
    
    if ( !(isDestTainted || isCountTainted || isCarryFlagTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais mémoire et/ou carry oui) => cas RCL_IM
    else if (!isCountTainted)  sRCL_IM<lengthInBits>(tid, (UINT32) regCLValue, writeAddress, regGflagsValue ,insAddress); 
    else // déplacement marqué  
    {
        _LOGTAINT(tid, insAddress, "RCL_RM" + decstr(lengthInBits));
            
        // création de l'objet Source correspondant à la mémoire
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)) 
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // récupération du déplacement (marqué)
        ObjectSource objCount(pTmgrTls->getRegisterTaint(REG_CL));

        // création de l'objet resultat de l'opération
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_RCL, objSrcMem, objSrcCF, objCount);

        // marquage flags
        // CF/RCL : recopie du dernier bit de la source ejecté à gauche 
        // c'est à dire bit 'lengthInBits - depl' de la source
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_CARRY_RCL, objSrcMem, objCount));
        // OF/RCL : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sRCL_RM

template<UINT32 lengthInBits> void ROTATE::sRCL_RR
    (THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT regGflagsValue , ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted     = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted      = pTmgrTls->isRegisterTainted<lengthInBits>(reg);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();
    
    if ( !(isDestTainted || isCountTainted || isCarryFlagTainted)) 
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais registre oui) => cas RCL_IR
    else if (!isCountTainted) sRCL_IR<lengthInBits>(tid, (UINT32) regCLValue, reg, regValue, regGflagsValue ,insAddress); 
    else // déplacement marqué 
    {
        _LOGTAINT(tid, insAddress, "RCL_RR" + decstr(lengthInBits));
         
        // création de l'objet Source correspondant au registre cible
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue))
            : ObjectSource(lengthInBits, regValue);

        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // récupération du déplacement (marqué)
        ObjectSource objCount(pTmgrTls->getRegisterTaint(REG_CL));

        // création de l'objet resultat de l'opération
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_RCL, objSrcReg, objSrcCF, objCount); 
     
        // marquage flags
        // CF/RCL : recopie du dernier bit de la source ejecté à gauche 
        // c'est à dire bit 'lengthInBits - depl' de la source
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_CARRY_RCL, objSrcReg, objCount));
        // OF/RCL : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sRCL_RR
     
/*********/
/** RCR **/
/*********/

template<UINT32 lengthInBits> void ROTATE::sRCR_IM
    (THREADID tid, UINT32 depl, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress)
{  
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isSrcTainted       = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();

    // opérandes non marquées => démarquage flags 
    if (!(isSrcTainted || isCarryFlagTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // MANUEL INTEL : 
        /* CASE (determine count) OF
        SIZE ← 8: tempCOUNT ← (COUNT AND 1FH) MOD 9;
        SIZE ← 16: tempCOUNT ← (COUNT AND 1FH) MOD 17;
        SIZE ← 32: tempCOUNT ← COUNT AND 1FH;
        SIZE ← 64: tempCOUNT ← COUNT AND 3FH;
        ESAC; */
        UINT32 tempDepl = 0;
        switch (lengthInBits)
        {
        case 8:  tempDepl = (depl & 0x1f) % 9;  break;
        case 16: tempDepl = (depl & 0x1f) % 17; break;
        case 32: tempDepl = (depl & 0x1f); break;
        case 64: tempDepl = (depl & 0x3f); break;
        }

        _LOGTAINT(tid, insAddress, "RCR_IM " + decstr(lengthInBits));

        // Récupération du marquage ou valeur de la mémoire
        ObjectSource objSrcMem = (isSrcTainted) 
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress))
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_RCR,
            objSrcMem,
            objSrcCF,
            ObjectSource(8, tempDepl));

        // marquage flags
        // CF/RCR : recopie du dernier bit de la source ejecté à droite (bit 'depl - 1' avec la source codée sur les bits de 0 à lengthInBits-1)
        UINT32 bitNumber = tempDepl - 1;
        TaintBitPtr cfPtr = std::make_shared<TaintBit>(EXTRACT, objSrcMem, ObjectSource(8, bitNumber));
        pTmgrTls->updateTaintCarryFlag(cfPtr);
        // OF/RCR ssi deplacement ORIGINAL vaut 1 
        if (depl == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
                F_OVERFLOW_ROL, // RCL : calcul identique à ROL
                ObjectSource(resultPtr),
                ObjectSource(cfPtr))); // CF apres la rotation, tout juste calculé
        }
        else pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sRCR_IM

template<UINT32 lengthInBits> void ROTATE::sRCR_IR
    (THREADID tid, UINT32 depl, REG reg, ADDRINT regValue, ADDRINT regGflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isSrcTainted       = pTmgrTls->isRegisterTainted<lengthInBits>(reg);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();
    
    // opérandes non marquées => démarquage flags 
    if (!(isSrcTainted || isCarryFlagTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    else 
    { 
        // MANUEL INTEL : 
        /* CASE (determine count) OF
        SIZE ← 8: tempCOUNT ← (COUNT AND 1FH) MOD 9;
        SIZE ← 16: tempCOUNT ← (COUNT AND 1FH) MOD 17;
        SIZE ← 32: tempCOUNT ← COUNT AND 1FH;
        SIZE ← 64: tempCOUNT ← COUNT AND 3FH;
        ESAC; */
        UINT32 tempDepl = 0;
        switch (lengthInBits)
        {
        case 8:  tempDepl = (depl & 0x1f) % 9;  break;
        case 16: tempDepl = (depl & 0x1f) % 17; break;
        case 32: tempDepl = (depl & 0x1f); break;
        case 64: tempDepl = (depl & 0x3f); break;
        }
    
        _LOGTAINT(tid, insAddress, "RCR_IR " + decstr(lengthInBits));
        
        // Récupération du marquage ou valeur du registre
        ObjectSource objSrcReg = (isSrcTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue))
            : ObjectSource(lengthInBits, regValue);
        
        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(
            X_RCR,
            objSrcReg,
            objSrcCF,
            ObjectSource(8, tempDepl));

        // marquage flags
        // CF/RCR : recopie du dernier bit de la source ejecté à droite (bit 'depl - 1' avec la source codée sur les bits de 0 à lengthInBits-1)
        UINT32 bitNumber = tempDepl - 1;
        TaintBitPtr cfPtr = std::make_shared<TaintBit>(EXTRACT, objSrcReg, ObjectSource(8, bitNumber));
        pTmgrTls->updateTaintCarryFlag(cfPtr);
        // OF/RCR ssi deplacement ORIGINAL vaut 1 
        if (depl == 1)
        {
            pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
                F_OVERFLOW_ROL, // RCL : calcul identique à ROL
                ObjectSource(resultPtr),
                ObjectSource(cfPtr))); // CF apres la rotation, tout juste calculé
        }
        else pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sRCR

template<UINT32 lengthInBits> void ROTATE::sRCR_RM
    (THREADID tid, ADDRINT regCLValue, ADDRINT writeAddress, ADDRINT regGflagsValue, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted     = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted      = pTmgrGlobal->isMemoryTainted<lengthInBits>(writeAddress);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();
    
    if ( !(isDestTainted || isCountTainted || isCarryFlagTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais mémoire et/ou carry oui) => cas RCR_IM
    else if (!isCountTainted) sRCR_IM<lengthInBits>(tid, (UINT32) regCLValue, writeAddress, regGflagsValue ,insAddress); 
    else // déplacement marqué  
    {
        _LOGTAINT(tid, insAddress, "RCR_RM" + decstr(lengthInBits));
            
        // création de l'objet Source correspondant à la mémoire
        ObjectSource objSrcMem = (isDestTainted)
            ? ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(writeAddress)) 
            : ObjectSource(lengthInBits, getMemoryValue<lengthInBits>(writeAddress));

        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // récupération du déplacement (marqué)
        ObjectSource objCount(pTmgrTls->getRegisterTaint(REG_CL));

        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_RCR, objSrcMem, objSrcCF, objCount);

        // marquage flags
        // CF/RCR : recopie du dernier bit de la source ejecté à droite 
        // c'est à dire bit 'depl - 1' de la source
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_CARRY_RCR, objSrcMem, objCount));
        // OF/RCR : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(writeAddress, resultPtr);
    }
} // sRCR_RM

template<UINT32 lengthInBits> void ROTATE::sRCR_RR
    (THREADID tid, ADDRINT regCLValue, REG reg, ADDRINT regValue, ADDRINT regGflagsValue , ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isCountTainted     = pTmgrTls->isRegisterTainted<8>(REG_CL);
    bool isDestTainted      = pTmgrTls->isRegisterTainted<lengthInBits>(reg);
    bool isCarryFlagTainted = pTmgrTls->isCarryFlagTainted();
    
    if ( !(isDestTainted || isCountTainted || isCarryFlagTainted))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintOverflowFlag();
    }
    // déplacement non marqué (mais registre oui) => cas RCL_IR
    else if (!isCountTainted) sRCR_IR<lengthInBits>(tid, (UINT32) regCLValue, reg, regValue, regGflagsValue ,insAddress); 
    else // déplacement marqué 
    {
        _LOGTAINT(tid, insAddress, "RCR_RR" + decstr(lengthInBits));
         
        // création de l'objet Source correspondant au registre cible
        ObjectSource objSrcReg = (isDestTainted)
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(reg, regValue))
            : ObjectSource(lengthInBits, regValue);

        // Récupération du Carry Flag (marqué ou valeur);
        ObjectSource objSrcCF = (isCarryFlagTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, (regGflagsValue >> CARRY_FLAG) & 1);

        // récupération du déplacement (marqué)
        ObjectSource objCount(pTmgrTls->getRegisterTaint(REG_CL));

        // construction du résultat
        TAINT_OBJECT_PTR resultPtr = MK_TAINT_OBJECT_PTR(X_RCR, objSrcReg, objSrcCF, objCount);
    
        // marquage flags
        // CF/RCR : recopie du dernier bit de la source ejecté à droite 
        // c'est à dire bit 'depl - 1' de la source
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_CARRY_RCR, objSrcReg, objCount));
        // OF/RCR : démarquage si déplacement marqué (tant pis : sous-marquage si la valeur est de 1...)
        pTmgrTls->unTaintOverflowFlag();

        // marquage destination
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, resultPtr);
    }
} // sRCR_RR