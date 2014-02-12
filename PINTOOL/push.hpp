// déclaration des templates du namespace PUSH

template<UINT32 len> void PUSH::sUpdateEspTaint(TaintManager_Thread *pTmgrTls, ADDRINT stackAddressBeforePush)
{
    // le PUSH décrémente ESP/RSP de 'len >> 3'
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP - (longueur pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(32, len >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = RSP - (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, len >> 3)));
    }
#endif
}

template<UINT32 len> 
void PUSH::sPUSH_M(THREADID tid, ADDRINT readAddress, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    // ajustement du marquage d'ESP si besoin
    PUSH::sUpdateEspTaint<len>(pTmgrTls, stackAddressBeforePush);

    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT espAddress = stackAddressBeforePush - (len >> 3); 
    
    if ( !pTmgrGlobal->isMemoryTainted<len>(readAddress))  pTmgrGlobal->unTaintMemory<len>(espAddress);
    else 
    {
        do
        {
            if (pTmgrGlobal->isMemoryTainted<8>(readAddress)) // octet source marqué ?
            {    
                _LOGTAINT("PUSHM" << len);
                // marquage de l'octet de la pile avec l'octet de la mémoire
                pTmgrGlobal->updateMemoryTaint<8>(espAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));    
            }
            else  pTmgrGlobal->unTaintMemory<8>(espAddress);    // sinon démarquage
            ++readAddress;
        } while (++espAddress < stackAddressBeforePush); 
    }
} //sPUSH_M

template<UINT32 len> void PUSH::sPUSH_R(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
    
    // ajustement du marquage d'ESP si besoin
    PUSH::sUpdateEspTaint<len>(pTmgrTls, stackAddressBeforePush);
    
    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT espAddress = stackAddressBeforePush - (len >> 3); 

    if ( !pTmgrTls->isRegisterTainted<len>(reg))   pTmgrGlobal->unTaintMemory<len>(espAddress);
    else 
    {
        REGINDEX regIndex = getRegIndex(reg);   
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart, ++espAddress) 
        {
            if (pTmgrTls->isRegisterPartTainted(regIndex, regPart)) // octet marqué ?
            {    
                _LOGTAINT("PUSHR" << len << " octet " << regPart);
                pTmgrGlobal->updateMemoryTaint<8>(espAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart))));    
            }   
            else pTmgrGlobal->unTaintMemory<8>(espAddress);    // sinon démarquage
        }
    }
} // sPUSH_R

template<UINT32 len> void PUSH::sPUSH_R_STACK(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
   
    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT stackAddressForPush = stackAddressBeforePush - (len >> 3); 

    // le cas ou reg vaut SP/ESP/RSP impose un traitement plus compliqué...sauf si non marqué
    if (! pTmgrTls->isRegisterTainted<len>(reg)) 
    {
        pTmgrGlobal->unTaintMemory<len>(stackAddressForPush);
    }
    else
    {
        // récupération du marquage du registre de pile
        std::shared_ptr<TaintObject<len>> tPtr = 
            pTmgrTls->getRegisterTaint<len>(reg, stackAddressBeforePush);
        
        // PUSH : stockage de ce marquage à l'adresse de push
        pTmgrGlobal->updateMemoryTaint<len>(stackAddressForPush, std::make_shared<TaintObject<len>>(
            X_ASSIGN,
            ObjectSource(tPtr)));
        
        // création du nouveau marquage du registre de pile : soustraction de 'len >> 3' octets
        std::shared_ptr<TaintObject<len>> tPtrAfterPush = std::make_shared<TaintObject<len>>(
            X_SUB,
            ObjectSource(tPtr),
            ObjectSource(len, len >> 3));

        // mise à jour du marquage du registre avec ce nouvel objet
        pTmgrTls->updateTaintRegister<len>(reg, tPtrAfterPush);
    }
} // sPUSH_R_STACK

template<UINT32 len> void PUSH::sPUSH_I(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
   
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    PUSH::sUpdateEspTaint<len>(pTmgrTls, stackAddressBeforePush);

    // PUSH valeur => démarquage
    pTmgrGlobal->unTaintMemory<len>(stackAddressBeforePush - (len >> 3));
} // sPUSH_I

template<UINT32 len>
void PUSH::sPUSHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT stackAddressBeforePush ADDRESS_DEBUG)
{
    // len == 16 <-> PUSHF, len == 32 <-> PUSHFD, len == 64 <-> PUSHFQ
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
     
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    PUSH::sUpdateEspTaint<len>(pTmgrTls, stackAddressBeforePush);

    // mise sur la pile du registre des flags
    // dans le cadre du marquage, on va construire un TaintWord formé par la concaténation
    // des 16 bits faibles des flags, avec le marquage des drapeaux suivis ou leur valeur
    // les autres bits des Flags (> 16) ne nous intéressent pas => démarquage
    
    vector<TaintBitPtr> vFlagsPtr(16);
    // récupération du marquage des flags suivis
    vFlagsPtr[CARRY_FLAG]     = pTmgrTls->getTaintCarryFlag();
    vFlagsPtr[PARITY_FLAG]    = pTmgrTls->getTaintParityFlag();
    vFlagsPtr[AUXILIARY_FLAG] = pTmgrTls->getTaintAuxiliaryFlag();
    vFlagsPtr[ZERO_FLAG]      = pTmgrTls->getTaintZeroFlag();
    vFlagsPtr[SIGN_FLAG]      = pTmgrTls->getTaintSignFlag();
    vFlagsPtr[OVERFLOW_FLAG]  = pTmgrTls->getTaintOverflowFlag();

    TaintWord twConcat(CONCAT);
    for (auto it = vFlagsPtr.begin() ; it != vFlagsPtr.end() ; ++it, regFlagsValue >>= 1)
    {
        // si flags non marqué ou non suivi : insérer la valeur du flag
        if (nullptr == *it) twConcat.addConstantAsASource<1>(regFlagsValue & 1);
        // sinon insérer l'objet marqué
        else twConcat.addSource(*it);
    }

    // marquage de l'adresse [addr - 'taille' ; addr - 'taille + 2'[ avec ce TaintWord
    ADDRINT startAddress = stackAddressBeforePush - (len >> 3); // adresse de push des octets
    pTmgrGlobal->updateMemoryTaint<16>(startAddress, std::make_shared<TaintWord>(twConcat));

    // démarquage des octets représentant les octets forts des flags
    startAddress += 2;  // adresse après le push des 2 octets des flags
    while (startAddress < stackAddressBeforePush)   pTmgrGlobal->unTaintMemory<8>(startAddress++);

} // sPUSHF
