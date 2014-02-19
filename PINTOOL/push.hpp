// déclaration des templates du namespace PUSH

template<UINT32 lengthInBits> void PUSH::sUpdateEspTaint(TaintManager_Thread *pTmgrTls, ADDRINT stackAddressBeforePush)
{
    // le PUSH décrémente ESP/RSP de 'lengthInBits >> 3'
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP - (longueur pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(32, lengthInBits >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = RSP - (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, lengthInBits >> 3)));
    }
#endif
}

template<UINT32 lengthInBits> 
void PUSH::sPUSH_M(THREADID tid, ADDRINT readAddress, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // ajustement du marquage d'ESP si besoin
    PUSH::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePush);

    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT espAddress = stackAddressBeforePush - (lengthInBits >> 3); 
    
    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(readAddress))  pTmgrGlobal->unTaintMemory<lengthInBits>(espAddress);
    else 
    {
        do
        {
            if (pTmgrGlobal->isMemoryTainted<8>(readAddress)) // octet source marqué ?
            {    
                _LOGTAINT("PUSHM" << lengthInBits);
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

template<UINT32 lengthInBits> void PUSH::sPUSH_R(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    
    
    // ajustement du marquage d'ESP si besoin
    PUSH::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePush);
    
    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT espAddress = stackAddressBeforePush - (lengthInBits >> 3); 

    if ( !pTmgrTls->isRegisterTainted<lengthInBits>(reg))   pTmgrGlobal->unTaintMemory<lengthInBits>(espAddress);
    else 
    {
        REGINDEX regIndex = getRegIndex(reg);   
        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart, ++espAddress) 
        {
            if (pTmgrTls->isRegisterPartTainted(regIndex, regPart)) // octet marqué ?
            {    
                _LOGTAINT("PUSHR" << lengthInBits << " octet " << regPart);
                pTmgrGlobal->updateMemoryTaint<8>(espAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart))));    
            }   
            else pTmgrGlobal->unTaintMemory<8>(espAddress);    // sinon démarquage
        }
    }
} // sPUSH_R

template<UINT32 lengthInBits> void PUSH::sPUSH_R_STACK(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    
   
    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT stackAddressForPush = stackAddressBeforePush - (lengthInBits >> 3); 

    // le cas ou reg vaut SP/ESP/RSP impose un traitement plus compliqué...sauf si non marqué
    if (! pTmgrTls->isRegisterTainted<lengthInBits>(reg)) 
    {
        pTmgrGlobal->unTaintMemory<lengthInBits>(stackAddressForPush);
    }
    else
    {
        // récupération du marquage du registre de pile
        TAINT_OBJECT_PTR tPtr = 
            pTmgrTls->getRegisterTaint<lengthInBits>(reg, stackAddressBeforePush);
        
        // PUSH : stockage de ce marquage à l'adresse de push
        pTmgrGlobal->updateMemoryTaint<lengthInBits>(stackAddressForPush, MK_TAINT_OBJECT_PTR(
            X_ASSIGN,
            ObjectSource(tPtr)));
        
        // création du nouveau marquage du registre de pile : soustraction de 'lengthInBits >> 3' octets
        TAINT_OBJECT_PTR tPtrAfterPush = MK_TAINT_OBJECT_PTR(
            X_SUB,
            ObjectSource(tPtr),
            ObjectSource(lengthInBits, lengthInBits >> 3));

        // mise à jour du marquage du registre avec ce nouvel objet
        pTmgrTls->updateTaintRegister<lengthInBits>(reg, tPtrAfterPush);
    }
} // sPUSH_R_STACK

template<UINT32 lengthInBits> void PUSH::sPUSH_I(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    
   
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    PUSH::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePush);

    // PUSH valeur => démarquage
    pTmgrGlobal->unTaintMemory<lengthInBits>(stackAddressBeforePush - (lengthInBits >> 3));
} // sPUSH_I

template<UINT32 lengthInBits>
void PUSH::sPUSHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT stackAddressBeforePush ADDRESS_DEBUG)
{
    // lengthInBits == 16 <-> PUSHF, lengthInBits == 32 <-> PUSHFD, lengthInBits == 64 <-> PUSHFQ
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    
     
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    PUSH::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePush);

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
    ADDRINT startAddress = stackAddressBeforePush - (lengthInBits >> 3); // adresse de push des octets
    pTmgrGlobal->updateMemoryTaint<16>(startAddress, std::make_shared<TaintWord>(twConcat));

    // démarquage des octets représentant les octets forts des flags
    startAddress += 2;  // adresse après le push des 2 octets des flags
    while (startAddress < stackAddressBeforePush)   pTmgrGlobal->unTaintMemory<8>(startAddress++);

} // sPUSHF
