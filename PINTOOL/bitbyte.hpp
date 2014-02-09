#include "TaintManager.h"

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
// -> la position du bit (0 à len-1) est quant à lui suivi en marquage


/*** BT : juste marquage de CF avec le bit concerné ***/

template<UINT32 len> void BITBYTE::sBT_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'len' = AND 'len-1')
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BT_IM" << len << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            ObjectSource(pTmgrGlobal->getMemoryTaint<8>(testedByte)),
            ObjectSource(8, testedBit)));		
    }
} // sBT_IM

template<UINT32 len> void BITBYTE::sBT_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64 
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BT_IR" << len << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);

        // extraction du bit et stockage dans CarryFlag; on prend l'index du bit dans l'octet testé.
        // Ex : bit 17 <=> bit 1 de l'octet 2 ; on calcule donc maskedValue % 8 (ou AND 0x7)
        UINT32 testedBit = maskedValue & 0x7;
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT,
            ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, testedByte)),
            ObjectSource(8, testedBit)));	
    }
} // sBT_IR

template<UINT32 len> void BITBYTE::sBT_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<len>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BT_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BT_IM
        {
            // calcul du modulo du déplacement 16/32/64 = position du bit dans le byte :)
            UINT32 testedBit = bitIndexRegValue & (len - 1);
            _LOGTAINT("BT_RM" << len << " depl non marqué ;  adresse (source et réelle) " \
                << hex << testedAddress << " " << testedByte << " depl " << dec << testedBit);
        
            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                EXTRACT,
                ObjectSource(pTmgrGlobal->getMemoryTaint<8>(testedByte)),
                ObjectSource(8, testedBit)));	
        }
        else // position du bit marqué (partie faible du registre marqué)
        {
            _LOGTAINT("BT_RM" << len << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                ObjectSource(pTmgrGlobal->getMemoryTaint<len>(testedByte)),
                ObjectSource(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue))));
        }
    }
}  // sBT_RM

template<UINT32 len> void BITBYTE::sBT_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<len>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<len>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BT_IR
    {
        sBT_IR<len>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée 
    {
        if (isTestedRegTainted) // registre testé est marqué
        {
            _LOGTAINT("BT_RR" << len << " registre "<< REG_StringShort(testedReg) << " MARQUE et depl NON marqué");

            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                ObjectSource(pTmgrTls->getRegisterTaint<len>(testedReg, testedRegValue)),
                ObjectSource(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue))));
        }
        else // registre testé est NON marqué
        {
            _LOGTAINT("BT_RR" << len << " registre "<< REG_StringShort(testedReg) << " non marqué et depl marqué");

            // extraction du bit et stockage dans CarryFlag
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                ObjectSource(len, testedRegValue),
                ObjectSource(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue))));
        }	
    }
} // sBT_RR

/*************************************/
/** BTC : test et Complément du bit **/
/*************************************/

template<UINT32 len> void BITBYTE::sBTC_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'len' = AND 'len-1')
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTC_IM" << len << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
        
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

template<UINT32 len> void BITBYTE::sBTC_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTC_IR" << len << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);

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

template<UINT32 len> void BITBYTE::sBTC_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit. Le bit testé sera compris entre 0 et 31 ou 63
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<len>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BTC_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BTC_IM
        {
            // calcul du modulo du déplacement 16/32/64 = position du bit dans le byte :)
            UINT32 maskedValue = bitIndexRegValue & (len - 1);

            _LOGTAINT("BTC_RM" << len << " depl non marqué ;  adresse (source et réelle) " \
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
            _LOGTAINT("BTC_RM" << len << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            ObjectSource objTestedMem(pTmgrGlobal->getMemoryTaint<len>(testedByte));
            ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue));

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                objTestedMem,
                objTestedBit));

            // BTC inversion du bit : COMPLEMENT_BIT (= XOR avec 1<<testedBit avec bit marqué)
            // le modulo sera inseré dans la formule SMTLIB
            pTmgrGlobal->updateMemoryTaint<len>(testedByte, std::make_shared<TaintObject<len>>(
                X_COMPLEMENT_BIT,
                objTestedMem,
                objTestedBit));
        }
    }
}  // sBTC_RM

template<UINT32 len> void BITBYTE::sBTC_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<len>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<len>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BTC_IR
    {
        sBTC_IR<len>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée (registre testé marqué ou non)
    {
        ObjectSource objTestedReg = (isTestedRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(testedReg, testedRegValue))
            : ObjectSource(len, testedRegValue);

        ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue));

        _LOGTAINT("BTC_RR" << len << " registre "<< REG_StringShort(testedReg) \
            << ((isTestedRegTainted) ? " MARQUE" : " ") << " depl marqué");

        // extraction du bit et stockage dans CarryFlag
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            F_CARRY_BITBYTE, 
            objTestedReg,
            objTestedBit));	

        // BTC inversion du bit : XOR avec 1<<testedBit (position du bit marqué)
        // le modulo sera inseré dans la formule SMTLIB
        pTmgrTls->updateTaintRegister<len>(testedReg, std::make_shared<TaintObject<len>>(
            X_COMPLEMENT_BIT, 
            objTestedReg,
            objTestedBit));	
    }
} // sBTC_RR

/***********************************/
/** BTR : test et mise à 0 du bit **/
/***********************************/

template<UINT32 len> void BITBYTE::sBTR_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'len' = AND 'len-1')
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTR_IM" << len << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
        
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

template<UINT32 len> void BITBYTE::sBTR_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTR_IR" << len << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);

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

template<UINT32 len> void BITBYTE::sBTR_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit. Le bit testé sera compris entre 0 et 31 ou 63
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<len>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BTR_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BTR_IM
        {
            // calcul du modulo du déplacement 16/32/64 = position du bit dans le byte :)
            UINT32 maskedValue = bitIndexRegValue & (len - 1);

            _LOGTAINT("BTR_RM" << len << " depl non marqué ;  adresse (source et réelle) " \
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
            _LOGTAINT("BTR_RM" << len << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            ObjectSource objTestedMem(pTmgrGlobal->getMemoryTaint<len>(testedByte));
            ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue));

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                objTestedMem,
                objTestedBit));

            // BTR mise a zero du bit : CLEAR_BIT (= AND avec NOT(1<<testedBit) lorsque bit marqué)
            // le modulo sera inseré dans la formule SMTLIB
            pTmgrGlobal->updateMemoryTaint<len>(testedByte, std::make_shared<TaintObject<len>>(
                X_CLEAR_BIT,
                objTestedMem,
                objTestedBit));
        }
    }
}  // sBTR_RM

template<UINT32 len> void BITBYTE::sBTR_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<len>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<len>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BTR_IR
    {
        sBTR_IR<len>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée (registre testé marqué ou non)
    {
        ObjectSource objTestedReg = (isTestedRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(testedReg, testedRegValue))
            : ObjectSource(len, testedRegValue);

        ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue));

        _LOGTAINT("BTR_RR" << len << " registre "<< REG_StringShort(testedReg) \
            << ((isTestedRegTainted) ? " MARQUE" : " ") << " depl marqué");

        // extraction du bit et stockage dans CarryFlag
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            F_CARRY_BITBYTE, 
            objTestedReg,
            objTestedBit));	

        // BTR mise a zero du bit : CLEAR_BIT (= AND avec NOT(1<<testedBit) lorsque bit marqué)
        // le modulo sera inseré dans la formule SMTLIB
        pTmgrTls->updateTaintRegister<len>(testedReg, std::make_shared<TaintObject<len>>(
            X_COMPLEMENT_BIT, 
            objTestedReg,
            objTestedBit));	
    }
} // sBTR_RR

/***********************************/
/** BTS : test et mise à 1 du bit **/
/***********************************/

template<UINT32 len> void BITBYTE::sBTS_IM(THREADID tid, ADDRINT testedAddress, ADDRINT value ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // calcul du modulo du déplacement 16/32/64 (NB : modulo 'len' = AND 'len-1')
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    ADDRINT testedByte = testedAddress + (maskedValue >> 3);

    if ( !pTmgrGlobal->isMemoryTainted<8>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTS_IM" << len << " adresse (source et réelle) "<< hex << testedAddress << " " << testedByte << " depl " << dec << maskedValue);
        
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

template<UINT32 len> void BITBYTE::sBTS_IR(THREADID tid, REG testedReg, ADDRINT value ADDRESS_DEBUG)
{
    REGINDEX regIndex = getRegIndex(testedReg);
    
    // calcul du modulo du déplacement 16/32/64 (optimisé en AND à la compilation)
    UINT32 maskedValue = value & (len - 1);
    // calcul de l'octet réellement concerné par le test (maskedValue DIV 8)
    UINT32 testedByte = maskedValue >> 3;  

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de l'octet concerné
    if ( !pTmgrTls->isRegisterPartTainted(regIndex, testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        _LOGTAINT("BTS_IR" << len << " registre "<< REG_StringShort(testedReg) << " octet " << testedByte << " depl " << maskedValue);
         
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

template<UINT32 len> void BITBYTE::sBTS_RM
    (THREADID tid, ADDRINT testedAddress, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    // calcul du deplacement en octets (2/4/8)* (offset DIV 16/32/64), soit une division par 8. 
    // !!! CAST EN INT POUR FAIRE UNE DIVISION SIGNEE
    ADDRDELTA displ = static_cast<ADDRDELTA>(bitIndexRegValue) >> 3;
    // calcul de l'adresse de base pour le test du bit. Le bit testé sera compris entre 0 et 31 ou 63
    ADDRINT testedByte = testedAddress + displ;

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // test du marquage de la plage d'adresse. Si non marqué => démarquage CF (meme si le registre est marqué)
    if ( !pTmgrGlobal->isMemoryTainted<len>(testedByte)) pTmgrTls->unTaintCarryFlag();
    else 
    {
        REGINDEX bitIndexRegIndex = getRegIndex(bitIndexReg);

        // si l'octet faible du registre non marqué (là ou se trouve la position du bit) non marqué 
        // => cas BTS_IM, repris ici en intégral
        if (!pTmgrTls->isRegisterPartTainted(bitIndexRegIndex, 0)) // BTS_IM
        {
            // calcul du modulo du déplacement 16/32/64
            UINT32 maskedValue = bitIndexRegValue & (len - 1);

            _LOGTAINT("BTS_RM" << len << " depl non marqué ;  adresse (source et réelle) " \
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
            _LOGTAINT("BTS_RM" << len << " depl marqué !! ;  adresse (source et réelle) " << hex << testedAddress);

            ObjectSource objTestedMem(pTmgrGlobal->getMemoryTaint<len>(testedByte));
            ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue));

            // extraction du bit et stockage dans CarryFlag. Le modulo de la valeur du registre
            // sera effectué dans la formule SMTLIB
            pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
                F_CARRY_BITBYTE, 
                objTestedMem,
                objTestedBit));

            // BTS mise a 1 du bit : SET_BIT (= OR avec (1<<testedBit) lorsque bit marqué)
            // le modulo sera inseré dans la formule SMTLIB
            pTmgrGlobal->updateMemoryTaint<len>(testedByte, std::make_shared<TaintObject<len>>(
                X_SET_BIT,
                objTestedMem,
                objTestedBit));
        }
    }
}  // sBTS_RM

template<UINT32 len> void BITBYTE::sBTS_RR
    (THREADID tid, REG testedReg, ADDRINT testedRegValue, REG bitIndexReg, ADDRINT bitIndexRegValue ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
        
    bool isbitIndexTainted  = pTmgrTls->isRegisterTainted<len>(bitIndexReg);
    bool isTestedRegTainted = pTmgrTls->isRegisterTainted<len>(testedReg);

    if (!(isbitIndexTainted || isTestedRegTainted)) return; // source et position non marqués
    else if (!isbitIndexTainted) // position non marquée => cas BTS_IR
    {
        sBTS_IR<len>(tid, testedReg, bitIndexRegValue INSADDRESS);
    }
    else // cas position marquée (registre testé marqué ou non)
    {
        ObjectSource objTestedReg = (isTestedRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<len>(testedReg, testedRegValue))
            : ObjectSource(len, testedRegValue);

        ObjectSource objTestedBit(pTmgrTls->getRegisterTaint<len>(bitIndexReg, bitIndexRegValue));

        _LOGTAINT("BTS_RR" << len << " registre "<< REG_StringShort(testedReg) \
            << ((isTestedRegTainted) ? " MARQUE" : " ") << " depl marqué");

        // extraction du bit et stockage dans CarryFlag
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            F_CARRY_BITBYTE, 
            objTestedReg,
            objTestedBit));	

        // BTS mise a 1 du bit : SET_BIT (= OR avec (1<<testedBit) lorsque bit marqué)
        // le modulo sera inseré dans la formule SMTLIB
        pTmgrTls->updateTaintRegister<len>(testedReg, std::make_shared<TaintObject<len>>(
            X_SET_BIT,
            objTestedReg,
            objTestedBit));
    }
} // sBTS_RR


template<UINT32 len> void BITBYTE::sBSR_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG){ } 
template<UINT32 len> void BITBYTE::sBSR_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG resultReg ADDRESS_DEBUG){ } 

template<UINT32 len> void BITBYTE::sBSF_M(THREADID tid, ADDRINT testedAddress, REG resultReg ADDRESS_DEBUG){ } 
template<UINT32 len> void BITBYTE::sBSF_R(THREADID tid, REG testedReg, ADDRINT testedRegValue, REG resultReg ADDRESS_DEBUG){ }