// déclaration des templates du namespace POP

template<UINT32 len> void POP::sUpdateEspTaint(TaintManager_Thread *pTmgrTls, ADDRINT stackAddressBeforePush)
{
    // le POP incrémente ESP/RSP de 'len >> 3'
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP + (longueur pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(32, len >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = RSP + (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, len >> 3)));
    }
#endif
}

template<UINT32 len> 
void POP::sPOP_M(THREADID tid, ADDRINT writeAddress, ADDRINT stackAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // ajustement du marquage d'ESP si besoin
    POP::sUpdateEspTaint<len>(pTmgrTls, stackAddress);

    if ( !pTmgrGlobal->isMemoryTainted<len>(stackAddress)) pTmgrGlobal->unTaintMemory<len>(writeAddress); 
    else 
    {
        // numéro de l'octet traité
        UINT32 byteNumber = 0;
        do  
        {
            if (pTmgrGlobal->isMemoryTainted<8>(stackAddress))  
            {
                _LOGTAINT("popM" << len << " octet " << byteNumber);
                // marquage de l'octet de la mémoire avec l'octet présent sur la pile
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddress))));
            }
            else pTmgrGlobal->unTaintMemory<8>(writeAddress);
            ++writeAddress;
            ++stackAddress; 
        } while (++byteNumber < (len >> 3)); 
    }
} // sPOP_M

template<UINT32 len> 
void POP::sPOP_R(THREADID tid, REG regDest, ADDRINT stackAddress ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));
    
    // ajustement du marquage d'ESP si besoin, sauf dans le cas "POP ESP"
    // Manuel Intel  "the POP ESP instruction increments the stack pointer (ESP) 
    // before data at the old top of stack is written into the destination."
    // donc aucun ajustement après désempilage
    REGINDEX regIndex = getRegIndex(regDest);
#if TARGET_IA32
    if (rESP == regIndex)
#else
    if (rRSP == regIndex)
#endif
    {
        POP::sUpdateEspTaint<len>(pTmgrTls, stackAddress);
    }

    if ( !pTmgrGlobal->isMemoryTainted<len>(stackAddress)) pTmgrTls->unTaintRegister<len>(regDest); 
    else 
    {
        // copier coller de la procédure MOVMR<len>
        for (UINT32 regPart = 0 ; regPart < (len >> 3) ; ++regPart, ++stackAddress)
        {
            if (pTmgrGlobal->isMemoryTainted<8>(stackAddress))  // octet marqué ? 
            {	
                _LOGTAINT("POPR" << len << " octet " << regPart);	
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    X_ASSIGN, 
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddress))));
            }
            else pTmgrTls->unTaintRegisterPart(regIndex, regPart);
        }
    }
} // sPOP_R

template<UINT32 len>
void POP::sPOPF(THREADID tid, ADDRINT stackAddress ADDRESS_DEBUG)
{
    // len == 16 <-> POPF, len == 32 <-> POPFD, len == 64 <-> POPFQ
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
     
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    POP::sUpdateEspTaint<len>(pTmgrTls, stackAddress);

    // récupération du marquage des 8 bits faibles de la pile;  si non marqué,
    // alors démarquage CF/PF/AF/ZF/SF
    if (! pTmgrGlobal->isMemoryTainted<8>(stackAddress))
    {
        pTmgrTls->unTaintAuxiliaryFlag();
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintParityFlag();
        pTmgrTls->unTaintZeroFlag();
        pTmgrTls->unTaintSignFlag();
    }
    else 
    {
        // récupération du marquage de l'octet
        ObjectSource osFirstByte(pTmgrGlobal->getMemoryTaint<8>(stackAddress));
        
        // mise à jour du marquage de chaque flag
        pTmgrTls->updateTaintCarryFlag (std::make_shared<TaintBit>(
            EXTRACT, osFirstByte, ObjectSource(8, CARRY_FLAG)));
        pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(
            EXTRACT, osFirstByte, ObjectSource(8, PARITY_FLAG)));
        pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(
            EXTRACT, osFirstByte, ObjectSource(8, AUXILIARY_FLAG)));
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(
            EXTRACT, osFirstByte, ObjectSource(8, ZERO_FLAG)));
        pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(
            EXTRACT, osFirstByte, ObjectSource(8, SIGN_FLAG)));
    }

    // Overflow : test de l'octet (stack+1)
    if (! pTmgrGlobal->isMemoryTainted<8>(stackAddress + 1)) pTmgrTls->unTaintOverflowFlag();
    else
    {
        // mise à jour OF, valeur d'extraction ajustée (position - 8)
        pTmgrTls->updateTaintOverflowFlag(std::make_shared<TaintBit>(
            EXTRACT, 
            ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddress + 1)),
            ObjectSource(8, OVERFLOW_FLAG)));
    }
} // sPOPF