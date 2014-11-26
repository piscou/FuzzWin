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
void PUSH::sPUSH_M(THREADID tid, ADDRINT readAddress, ADDRINT stackAddressBeforePush, ADDRINT insAddress) 
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
                _LOGTAINT(tid, insAddress, "PUSHM" + decstr(lengthInBits));
                // marquage de l'octet de la pile avec l'octet de la mémoire
                pTmgrGlobal->updateMemoryTaint<8>(espAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));    
            }
            else  pTmgrGlobal->unTaintMemory<8>(espAddress);    // sinon démarquage
            ++readAddress;
            ++espAddress;
        } while (espAddress < stackAddressBeforePush); 
    }
} //sPUSH_M

template<UINT32 lengthInBits> void PUSH::sPUSH_R(THREADID tid, REG reg, ADDRINT stackAddressBeforePush, ADDRINT insAddress) 
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
                _LOGTAINT(tid, insAddress, "PUSHR" + decstr(lengthInBits) + " octet " + decstr(regPart));
                pTmgrGlobal->updateMemoryTaint<8>(espAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrTls->getRegisterPartTaint(regIndex, regPart))));    
            }   
            else pTmgrGlobal->unTaintMemory<8>(espAddress);    // sinon démarquage
        }
    }
} // sPUSH_R

template<UINT32 lengthInBits> void PUSH::sPUSH_R_STACK(THREADID tid, REG reg, ADDRINT stackAddressBeforePush, ADDRINT insAddress) 
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

template<UINT32 lengthInBits> void PUSH::sPUSH_I(THREADID tid, ADDRINT stackAddressBeforePush, ADDRINT insAddress)
{ 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    
   
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    PUSH::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePush);

    // PUSH valeur => démarquage
    pTmgrGlobal->unTaintMemory<lengthInBits>(stackAddressBeforePush - (lengthInBits >> 3));
} // sPUSH_I

template<UINT32 lengthInBits>
void PUSH::sPUSHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT stackAddressBeforePush, ADDRINT insAddress)
{
    // lengthInBits == 16 <-> PUSHF, lengthInBits == 32 <-> PUSHFD, lengthInBits == 64 <-> PUSHFQ
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    

    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    PUSH::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePush);

    // adresse de push des octets
    ADDRINT workingAddress = stackAddressBeforePush - (lengthInBits >> 3); 

    // test et marquage du 1er octet
    bool isCfTainted = pTmgrTls->isCarryFlagTainted();
    bool isPfTainted = pTmgrTls->isParityFlagTainted();
    bool isAfTainted = pTmgrTls->isAuxiliaryFlagTainted();
    bool isZfTainted = pTmgrTls->isZeroFlagTainted();
    bool isSfTainted = pTmgrTls->isSignFlagTainted();

    if (! (isCfTainted || isPfTainted || isAfTainted || isZfTainted || isSfTainted))
    {
        pTmgrGlobal->unTaintMemory<8>(workingAddress);  // démarquer le premier octet
    }
    else    // 1er octet = SF:ZF:??:AF:??:PF:??:CF
    {
        TaintByte firstTaintedByte(CONCAT);
        
        // 0 : CF
        firstTaintedByte.addSource((isCfTainted) 
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, EXTRACTBIT(regFlagsValue, CARRY_FLAG)));
        // 1 : N/A
        firstTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 1));
        // 2 : PF
        firstTaintedByte.addSource((isPfTainted) 
            ? ObjectSource(pTmgrTls->getTaintParityFlag())
            : ObjectSource(1, EXTRACTBIT(regFlagsValue, PARITY_FLAG)));
        // 3 : N/A
        firstTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 3));
        // 4 : AF
        firstTaintedByte.addSource((isAfTainted) 
            ? ObjectSource(pTmgrTls->getTaintAuxiliaryFlag())
            : ObjectSource(1, EXTRACTBIT(regFlagsValue, AUXILIARY_FLAG)));
        // 5 : NA
        firstTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 5));
        // 6 : ZF
        firstTaintedByte.addSource((isZfTainted) 
            ? ObjectSource(pTmgrTls->getTaintZeroFlag())
            : ObjectSource(1, EXTRACTBIT(regFlagsValue, ZERO_FLAG)));
        // 7 : SF
        firstTaintedByte.addSource((isSfTainted) 
            ? ObjectSource(pTmgrTls->getTaintSignFlag())
            : ObjectSource(1, EXTRACTBIT(regFlagsValue, SIGN_FLAG)));

        pTmgrGlobal->updateMemoryTaint<8>(workingAddress, 
            std::make_shared<TaintByte>(firstTaintedByte));
    }

    // test et marquage du 2eme octet
    ++workingAddress;
    if ( ! pTmgrTls->isOverflowFlagTainted())
    {
        pTmgrGlobal->unTaintMemory<8>(workingAddress);  // démarquer le second octet
    }
    else  // 2eme octet = ??:??:??:??:OF:??:??:??
    {
        TaintByte secondTaintedByte(CONCAT);
        // 8, 9, 10 : N/A
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 8));
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 9));
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 10));
        // 11 : OF forcément marqué
        secondTaintedByte.addSource(pTmgrTls->getTaintOverflowFlag());
        // 12, 13, 14, 15 : N/A
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 12));
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 13));
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 14));
        secondTaintedByte.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, 15));

        pTmgrGlobal->updateMemoryTaint<8>(workingAddress, 
            std::make_shared<TaintByte>(secondTaintedByte));
    }

    // démarquage des octets représentant les octets forts des flags
    // PUSHF : AUCUN,  PUSHFD : 2 octets,  PUSHFQ : 6 octets
    ++workingAddress;  // adresse du 3eme octet
    while (workingAddress < stackAddressBeforePush)   pTmgrGlobal->unTaintMemory<8>(workingAddress++);
} // sPUSHF
