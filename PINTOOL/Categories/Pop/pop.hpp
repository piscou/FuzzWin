// déclaration des templates du namespace POP

template<UINT32 lengthInBits> 
void POP::sUpdateEspTaint(TaintManager_Thread *pTmgrTls, ADDRINT stackAddressBeforePush)
{
    // le POP incrémente ESP/RSP de 'lengthInBits >> 3'
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP + (longueur pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(32, lengthInBits >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = RSP + (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_ADD, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, lengthInBits >> 3)));
    }
#endif
}

template<UINT32 lengthInBits> 
void POP::sPOP_M(THREADID tid, ADDRINT writeAddress, ADDRINT stackAddressBeforePop, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // ajustement du marquage d'ESP si besoin
    POP::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePop);

    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(stackAddressBeforePop)) pTmgrGlobal->unTaintMemory<lengthInBits>(writeAddress); 
    else 
    {
        // numéro de l'octet traité
        UINT32 byteNumber = 0;
        do  
        {
            if (pTmgrGlobal->isMemoryTainted<8>(stackAddressBeforePop))  
            {
                _LOGTAINT(tid, insAddress, "popM" + decstr(lengthInBits) + " octet " + decstr(byteNumber));
                // marquage de l'octet de la mémoire avec l'octet présent sur la pile
                pTmgrGlobal->updateMemoryTaint<8>(writeAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddressBeforePop))));
            }
            else pTmgrGlobal->unTaintMemory<8>(writeAddress);
            ++writeAddress;
            ++stackAddressBeforePop; 
            ++byteNumber;
        } while (byteNumber < (lengthInBits >> 3)); 
    }
} // sPOP_M

template<UINT32 lengthInBits> 
void POP::sPOP_R(THREADID tid, REG regDest, ADDRINT stackAddressBeforePop, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // ajustement du marquage d'ESP si besoin, sauf dans le cas "POP ESP"
    // Manuel Intel  "the POP ESP instruction increments the stack pointer (ESP) 
    // before data at the old top of stack is written into the destination."
    // donc aucun ajustement après désempilage
    REGINDEX regIndex = getRegIndex(regDest);
#if TARGET_IA32
    if (regIndexESP == regIndex)
#else
    if (regIndexRSP == regIndex)
#endif
    {
        POP::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddressBeforePop);
    }

    if ( !pTmgrGlobal->isMemoryTainted<lengthInBits>(stackAddressBeforePop)) pTmgrTls->unTaintRegister<lengthInBits>(regDest); 
    else 
    {
        // copier coller de la procédure MOVMR<lengthInBits>
        for (UINT32 regPart = 0 ; regPart < (lengthInBits >> 3) ; ++regPart, ++stackAddressBeforePop)
        {
            if (pTmgrGlobal->isMemoryTainted<8>(stackAddressBeforePop))  // octet marqué ? 
            {	
                _LOGTAINT(tid, insAddress, "POPR" + decstr(lengthInBits) + " octet " + decstr(regPart));	
                pTmgrTls->updateTaintRegisterPart(regIndex, regPart, std::make_shared<TaintByte>(
                    X_ASSIGN, 
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(stackAddressBeforePop))));
            }
            else pTmgrTls->unTaintRegisterPart(regIndex, regPart);
        }
    }
} // sPOP_R

template<UINT32 lengthInBits>
void POP::sPOPF(THREADID tid, ADDRINT stackAddress, ADDRINT insAddress)
{
    // lengthInBits == 16 <-> POPF, lengthInBits == 32 <-> POPFD, lengthInBits == 64 <-> POPFQ
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);    
     
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
    POP::sUpdateEspTaint<lengthInBits>(pTmgrTls, stackAddress);

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
            ObjectSource(8, OVERFLOW_FLAG - 8)));
    }
} // sPOPF