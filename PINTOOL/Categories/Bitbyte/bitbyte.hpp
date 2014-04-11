// Instruction BIT : plusieurs cas
// cible = registre => l'index du bit est le modulo de la source (immédiate ou registre)
// cible = memoire => si source immédiate, prendre son modulo 16/32/64
//                 => si source registre, l'octet cible est "ea + (2/4/8)* (offset DIV 16/32/64)"
//                    et le bit concerné = offset modulo 16/32/64
// cf manuel Intel pour BT et le calcul de l'adresse cible 

// !!!! LES CAS RM SONT TRAITES PARTIELLEMENT EN MARQUAGE !!!
// car considérant l'amplitude de parcours de la mémoire (de -2^31 à 2^31 par rapport 
// à l'adresse de base) il est impossible de modéliser le bit accédé en mémoire !!!!
// -> la position de l'octet sélectionné n'est pas suivi en marquage
// -> la position du bit (0 à lengthInBits-1) est quant à lui suivi en marquage


/*** BT : juste marquage de CF avec le bit concerné ***/

template<UINT32 lengthInBits> void BITBYTE::sBT_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'lengthInBits' = AND 'lengthInBits-1')
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BT_IM" << lengthInBits << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            ObjectSource(pTmgrGlobal->getMemoryTaint<8>(testedByte)),
            ObjectSource(8, testedBit)));		
    }
} // sBT_IM

template<UINT32 lengthInBits> void BITBYTE::sBT_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64 
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BT_IR" << lengthInBits << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, testedByte)),
            ObjectSource(8, testedBit)));	
    }
} // sBT_IR

template<UINT32 lengthInBits> void BITBYTE::sBT_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BT_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BT_IM
        {
            // calcul du modulo du déplacement 16/32/64 = position du bit dans le byte :)
            UINT32 testedBit = bitIndexRegValue & (lengthInBits - 1);
            _LOGTAINT("BT_RM" << lengthInBits << " depl non marqué ;  adresse (source et réelle) " \
                << hex << testedAddress << " " << testedByte << " depl " << dec << testedBit);
        
            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                EXTRACT,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(testedByte)),
                ObjectSource(8, testedBit)));	
        }
        else // position du bit marqué (partie faible du registre marqué)
        {
            _LOGTAINT("BT_RM" << lengthInBits << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                ObjectSource(pTmgrGlobal->getMemoryTaint<lengthInBits>(testedByte)),
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue))));
        }
    }
}  // sBT_RM

template<UINT32 lengthInBits> void BITBYTE::sBT_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BT_IR
    {
        sBT_IR<lengthInBits>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée 
    {
        if (isTestedRegTainted) // registre testé est marqué
        {
            _LOGTAINT("BT_RR" << lengthInBits << " registre "<< REG_StringShort(testedReg) << " MARQUE et depl NON marqué");

            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(testedReg, testedRegValue)),
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue))));
        }
        else // registre testé est NON marqué
        {
            _LOGTAINT("BT_RR" << lengthInBits << " registre "<< REG_StringShort(testedReg) << " non marqué et depl marqué");

            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                ObjectSource(lengthInBits, testedRegValue),
                ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue))));
        }	
    }
} // sBT_RR

/*************************************/
/** BTC : test et Complément du bit **/
/*************************************/

template<UINT32 lengthInBits> void BITBYTE::sBTC_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'lengthInBits' = AND 'lengthInBits-1')
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTC_IM" << lengthInBits << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
        
        ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(testedByte));
        
        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            objSrcMem,
            ObjectSource(8, testedBit)));		

        // BTC inversion du bit : XOR de l'octet marqué avec 1<<testedBit
        pTmgrGlobal->updateMemoryTaint<8>(testedByte, std::make_shared<TaintByte>(
            X_XOR,
            objSrcMem,
            ObjectSource(8, 1 << testedBit)));
    }
} // sBTC_IM

template<UINT32 lengthInBits> void BITBYTE::sBTC_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTC_IR" << lengthInBits << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);

         ObjectSource objSrcReg(pTmgrTls->getRegisterPartTaint(regIndex, testedByte));

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;

        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            objSrcReg,
            ObjectSource(8, testedBit)));		

        // BTC inversion du bit : XOR de l'octet marqué et concerné avec 1<<testedBit
        pTmgrTls->updateTaintRegisterPart(regIndex, testedByte, std::make_shared<TaintByte>(
            X_XOR,
            objSrcReg,
            ObjectSource(8, 1 << testedBit)));
    }
} // sBTC_IR

template<UINT32 lengthInBits> void BITBYTE::sBTC_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit. Le bit testé sera compris entre 0 et 31 ou 63
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BTC_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BTC_IM
        {
            // calcul du modulo du déplacement 16/32/64 = position du bit dans le byte :)
            UINT32 maskedValue = bitIndexRegValue & (lengthInBits - 1);

            _LOGTAINT("BTC_RM" << lengthInBits << " depl non marqué ;  adresse (source et réelle) " \
                << hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
 
            // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
            // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
            UINT32 testedBit = maskedValue & 0x7;
            ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(testedByte));
            
            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                EXTRACT,
                objSrcMem,
                ObjectSource(8, testedBit)));

            // BTC inversion du bit : XOR de l'octet marqué avec 1<<testedBit
            pTmgrGlobal->updateMemoryTaint<8>(testedByte, std::make_shared<TaintByte>(
                X_XOR,
                objSrcMem,
                ObjectSource(8, 1 << testedBit)));	
        }
        else // position du bit marqué (partie faible du registre marqué)
        {
            _LOGTAINT("BTC_RM" << lengthInBits << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            ObjectSource objTestedMem(pTmgrGlobal->getMemoryTaint<lengthInBits>(testedByte));
            ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue));

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                objTestedMem,
                objTestedBit));

            // BTC inversion du bit : COMPLEMENT_BIT (= XOR avec 1<<testedBit avec bit marqué)
            // le modulo sera inseré dans la formule SMTLIB
            pTmgrGlobal->updateMemoryTaint<lengthInBits>(testedByte, MK_TAINT_OBJECT_PTR(
                X_COMPLEMENT_BIT,
                objTestedMem,
                objTestedBit));
        }
    }
}  // sBTC_RM

template<UINT32 lengthInBits> void BITBYTE::sBTC_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BTC_IR
    {
        sBTC_IR<lengthInBits>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée (registre testé marqué ou non)
    {
        ObjectSource objTestedReg = (isTestedRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(testedReg, testedRegValue))
            : ObjectSource(lengthInBits, testedRegValue);

        ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue));

        _LOGTAINT("BTC_RR" << lengthInBits << " registre "<< REG_StringShort(testedReg) \
            << ((isTestedRegTainted) ? " MARQUE" : " ") << " depl marqué");

        // extraction du bit et stockage dans CarryFlag
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            F_CARRY_BITBYTE, 
            objTestedReg,
            objTestedBit));	

        // BTC inversion du bit : XOR avec 1<<testedBit (position du bit marqué)
        // le modulo sera inseré dans la formule SMTLIB
        pTmgrTls->updateTaintRegister<lengthInBits>(testedReg, MK_TAINT_OBJECT_PTR(
            X_COMPLEMENT_BIT, 
            objTestedReg,
            objTestedBit));	
    }
} // sBTC_RR

/***********************************/
/** BTR : test et mise à 0 du bit **/
/***********************************/

template<UINT32 lengthInBits> void BITBYTE::sBTR_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'lengthInBits' = AND 'lengthInBits-1')
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTR_IM" << lengthInBits << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
        
        ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(testedByte));
        
        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            objSrcMem,
            ObjectSource(8, testedBit)));		

        // BTR mise à 0 du bit : AND de l'octet marqué avec NOT(1<<testedBit)
        pTmgrGlobal->updateMemoryTaint<8>(testedByte, std::make_shared<TaintByte>(
            X_AND,
            objSrcMem,
            ObjectSource(8, ~(1 << testedBit))));
    }
} // sBTR_IM

template<UINT32 lengthInBits> void BITBYTE::sBTR_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTR_IR" << lengthInBits << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);

         ObjectSource objSrcReg(pTmgrTls->getRegisterPartTaint(regIndex, testedByte));

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;

        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            objSrcReg,
            ObjectSource(8, testedBit)));		

        // BTR mise à 0 du bit : AND de l'octet marqué avec NOT(1<<testedBit)
        pTmgrTls->updateTaintRegisterPart(regIndex, testedByte, std::make_shared<TaintByte>(
            X_AND,
            objSrcReg,
            ObjectSource(8, ~(1 << testedBit))));
    }
} // sBTR_IR

template<UINT32 lengthInBits> void BITBYTE::sBTR_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit. Le bit testé sera compris entre 0 et 31 ou 63
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BTR_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BTR_IM
        {
            // calcul du modulo du déplacement 16/32/64 = position du bit dans le byte :)
            UINT32 maskedValue = bitIndexRegValue & (lengthInBits - 1);

            _LOGTAINT("BTR_RM" << lengthInBits << " depl non marqué ;  adresse (source et réelle) " \
                << hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
 
            // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
            // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
            UINT32 testedBit = maskedValue & 0x7;
            ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(testedByte));
            
            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                EXTRACT,
                objSrcMem,
                ObjectSource(8, testedBit)));

            // BTR mise à zero du bit : AND de l'octet marqué avec NOT(1<<testedBit)
            pTmgrGlobal->updateMemoryTaint<8>(testedByte, std::make_shared<TaintByte>(
                X_AND,
                objSrcMem,
                ObjectSource(8, ~(1 << testedBit))));	
        }
        else // position du bit marqué (partie faible du registre marqué)
        {
            _LOGTAINT("BTR_RM" << lengthInBits << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            ObjectSource objTestedMem(pTmgrGlobal->getMemoryTaint<lengthInBits>(testedByte));
            ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue));

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                objTestedMem,
                objTestedBit));

            // BTR mise a zero du bit : CLEAR_BIT (= AND avec NOT(1<<testedBit) lorsque bit marqué)
            // le modulo sera inseré dans la formule SMTLIB
            pTmgrGlobal->updateMemoryTaint<lengthInBits>(testedByte, MK_TAINT_OBJECT_PTR(
                X_CLEAR_BIT,
                objTestedMem,
                objTestedBit));
        }
    }
}  // sBTR_RM

template<UINT32 lengthInBits> void BITBYTE::sBTR_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BTR_IR
    {
        sBTR_IR<lengthInBits>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée (registre testé marqué ou non)
    {
        ObjectSource objTestedReg = (isTestedRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(testedReg, testedRegValue))
            : ObjectSource(lengthInBits, testedRegValue);

        ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue));

        _LOGTAINT("BTR_RR" << lengthInBits << " registre "<< REG_StringShort(testedReg) \
            << ((isTestedRegTainted) ? " MARQUE" : " ") << " depl marqué");

        // extraction du bit et stockage dans CarryFlag
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            F_CARRY_BITBYTE, 
            objTestedReg,
            objTestedBit));	

        // BTR mise a zero du bit : CLEAR_BIT (= AND avec NOT(1<<testedBit) lorsque bit marqué)
        // le modulo sera inseré dans la formule SMTLIB
        pTmgrTls->updateTaintRegister<lengthInBits>(testedReg, MK_TAINT_OBJECT_PTR(
            X_COMPLEMENT_BIT, 
            objTestedReg,
            objTestedBit));	
    }
} // sBTR_RR

/***********************************/
/** BTS : test et mise à 1 du bit **/
/***********************************/

template<UINT32 lengthInBits> 
void BITBYTE::sBTS_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'lengthInBits' = AND 'lengthInBits-1')
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTS_IM" << lengthInBits << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
        
        ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(testedByte));
        
        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            objSrcMem,
            ObjectSource(8, testedBit)));		

        // BTS mise à 1 du bit : OR de l'octet marqué avec (1<<testedBit)
         pTmgrGlobal->updateMemoryTaint<8>(testedByte, std::make_shared<TaintByte>(
            X_OR,
            objSrcMem,
            ObjectSource(8, 1 << testedBit)));
    }
} // sBTS_IM

template<UINT32 lengthInBits> 
void BITBYTE::sBTS_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64 (optimisé en AND à la compilation)
    UINT32 maskedValue = value & (lengthInBits - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTS_IR" << lengthInBits << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);
         
        ObjectSource objSrcReg(pTmgrTls->getRegisterPartTaint(regIndex, testedByte));

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;

        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            objSrcReg,
            ObjectSource(8, testedBit)));		

        // BTS mise à 1 du bit : OR de l'octet marqué avec (1<<testedBit)
        pTmgrTls->updateTaintRegisterPart(regIndex, testedByte, std::make_shared<TaintByte>(
            X_OR,
            objSrcReg,
            ObjectSource(8, 1 << testedBit)));
    }
} // sBTS_IR

template<UINT32 lengthInBits> 
void BITBYTE::sBTS_RM(THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit. Le bit testé sera compris entre 0 et 31 ou 63
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BTS_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BTS_IM
        {
            // calcul du modulo du déplacement 16/32/64
            UINT32 maskedValue = bitIndexRegValue & (lengthInBits - 1);

            _LOGTAINT("BTS_RM" << lengthInBits << " depl non marqué ;  adresse (source et réelle) " \
                << hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
 
            // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
            // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
            UINT32 testedBit = maskedValue & 0x7;
            ObjectSource objSrcMem(pTmgrGlobal->getMemoryTaint<8>(testedByte));
            
            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                EXTRACT,
                objSrcMem,
                ObjectSource(8, testedBit)));		

            // BTS mise à 1 du bit : OR de l'octet marqué avec (1<<testedBit)
            pTmgrGlobal->updateMemoryTaint<8>(testedByte, std::make_shared<TaintByte>(
                X_OR,
                objSrcMem,
                ObjectSource(8, 1 << testedBit)));	
        }
        else // position du bit marqué (partie faible du registre marqué)
        {
            _LOGTAINT("BTS_RM" << lengthInBits << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            ObjectSource objTestedMem(pTmgrGlobal->getMemoryTaint<lengthInBits>(testedByte));
            ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue));

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                objTestedMem,
                objTestedBit));

            // BTS mise a 1 du bit : SET_BIT (= OR avec (1<<testedBit) lorsque bit marqué)
            // le modulo sera inseré dans la formule SMTLIB
            pTmgrGlobal->updateMemoryTaint<lengthInBits>(testedByte, MK_TAINT_OBJECT_PTR(
                X_SET_BIT,
                objTestedMem,
                objTestedBit));
        }
    }
}  // sBTS_RM

template<UINT32 lengthInBits> 
void BITBYTE::sBTS_RR(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<lengthInBits>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<lengthInBits>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BTS_IR
    {
        sBTS_IR<lengthInBits>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée (registre testé marqué ou non)
    {
        ObjectSource objTestedReg = (isTestedRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<lengthInBits>(testedReg, testedRegValue))
            : ObjectSource(lengthInBits, testedRegValue);

        ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<lengthInBits>(bitIndexReg, bitIndexRegValue));

        _LOGTAINT("BTS_RR" << lengthInBits << " registre "<< REG_StringShort(testedReg) \
            << ((isTestedRegTainted) ? " MARQUE" : " ") << " depl marqué");

        // extraction du bit et stockage dans CarryFlag
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            F_CARRY_BITBYTE, 
            objTestedReg,
            objTestedBit));	

        // BTS mise a 1 du bit : SET_BIT (= OR avec (1<<testedBit) lorsque bit marqué)
        // le modulo sera inseré dans la formule SMTLIB
        pTmgrTls->updateTaintRegister<lengthInBits>(testedReg, MK_TAINT_OBJECT_PTR(
            X_SET_BIT,
            objTestedReg,
            objTestedBit));
    }
} // sBTS_RR

/**********************************************/
/** BSR : Bit Scan Reverse (position du MSB) **/
/**********************************************/
template<UINT32 lengthInBits> 
void BITBYTE::sBSR_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if (! pTmgrGlobal->isMemoryTainted<lengthInBits>(testedAddress))
    {
        pTmgrTls->unTaintZeroFlag();
    }
    else
    {
        _LOGTAINT("BSR_M" << lengthInBits);

        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(testedAddress));

        // ZF vaut 1 si la source est nulle, 0 dans les autres cas => F_IS_NULL
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objSrc));

        // la destination vaut l'index du MSB => relation spécifique X_BSR
        pTmgrTls->updateTaintRegister<lengthInBits>(resultReg, MK_TAINT_OBJECT_PTR(X_BSR, objSrc));
    }
}  // sBSR_M

template<UINT32 lengthInBits> 
void BITBYTE::sBSR_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, 
                     REG resultReg ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if (! pTmgrTls->isRegisterTainted<lengthInBits>(testedReg))
    {
        pTmgrTls->unTaintZeroFlag();
    }
    else
    {
        _LOGTAINT("BSR_R" << lengthInBits);
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(testedReg, testedRegValue));

        // ZF vaut 1 si la source est nulle, 0 dans les autres cas => F_IS_NULL
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objSrc));

        // la destination vaut l'index du MSB => relation spécifique X_BSR
        pTmgrTls->updateTaintRegister<lengthInBits>(resultReg, MK_TAINT_OBJECT_PTR(X_BSR, objSrc));
    }
}  // sBSR_R 

/**********************************************/
/** BSF : Bit Scan Forward (position du LSB) **/
/**********************************************/
template<UINT32 lengthInBits> 
void BITBYTE::sBSF_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if (! pTmgrGlobal->isMemoryTainted<lengthInBits>(testedAddress))
    {
        pTmgrTls->unTaintZeroFlag();
    }
    else
    {
        _LOGTAINT("BSF_M" << lengthInBits);
        ObjectSource objSrc(pTmgrGlobal->getMemoryTaint<lengthInBits>(testedAddress));

        // ZF vaut 1 si la source est nulle, 0 dans les autres cas => F_IS_NULL
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objSrc));

        // la destination vaut l'index du LSB => relation spécifique X_BSF
        pTmgrTls->updateTaintRegister<lengthInBits>(resultReg, MK_TAINT_OBJECT_PTR(X_BSF, objSrc));
    }
}  // sBSF_M

template<UINT32 lengthInBits> 
void BITBYTE::sBSF_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, 
                     REG resultReg ADDRESS_DEBUG)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    if (! pTmgrTls->isRegisterTainted<lengthInBits>(testedReg))
    {
        pTmgrTls->unTaintZeroFlag();
    }
    else
    {
        _LOGTAINT("BSF_R" << lengthInBits);
        ObjectSource objSrc(pTmgrTls->getRegisterTaint<lengthInBits>(testedReg, testedRegValue));

        // ZF vaut 1 si la source est nulle, 0 dans les autres cas => F_IS_NULL
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objSrc));

        // la destination vaut l'index du MSB => relation spécifique X_BSF
        pTmgrTls->updateTaintRegister<lengthInBits>(resultReg, MK_TAINT_OBJECT_PTR(X_BSF, objSrc));
    }
}  // sBSF_R 