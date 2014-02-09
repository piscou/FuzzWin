#include "TaintManager.h"

template<UINT32 len> void PUSH::sPUSH_M(THREADID tid, ADDRINT readAddress, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{   
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));

    // adresse d'écriture sur la pile (on décrémente avant de "pusher")
    ADDRINT espAddress = stackAddressBeforePush - (len >> 3); 
    if ( !pTmgrGlobal->isMemoryTainted<len>(readAddress))  pTmgrGlobal->unTaintMemory<len>(espAddress);
    else 
    {
        do
        {
            if (pTmgrGlobal->isMemoryTainted<8>(readAddress)) // octet marqué ?
            {    
                _LOGTAINT("PUSHM" << len);
                pTmgrGlobal->updateMemoryTaint<8>(espAddress, std::make_shared<TaintByte>(
                    X_ASSIGN,
                    ObjectSource(pTmgrGlobal->getMemoryTaint<8>(readAddress))));    
            }
            else    pTmgrGlobal->unTaintMemory<8>(espAddress);    // sinon démarquage
            ++readAddress;
        } while (++espAddress < stackAddressBeforePush); 
    }
    
    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
#if TARGET_IA32
    if (pTmgrTls->isRegisterTainted<32>(REG_ESP))
    {
        // nouvel objet = ESP - (longueur memoire pushée)
        pTmgrTls->updateTaintRegister<32>(REG_ESP, std::make_shared<TaintDword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(32, len >> 3)));
    }
#else
    if (pTmgrTls->isRegisterTainted<64>(REG_RSP))
    {
        // nouvel objet = ESP - (longueur memoire pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, len >> 3)));
    }
#endif

} //sPUSH_M

template<UINT32 len> void PUSH::sPUSH_R(THREADID tid, REG reg, ADDRINT stackAddressBeforePush ADDRESS_DEBUG) 
{
    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
    
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

    // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
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
        // nouvel objet = ESP - (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, len >> 3)));
    }
#endif
} // sPUSH_R

template<UINT32 len> void PUSH::sPUSH_I(THREADID tid, ADDRINT stackAddressBeforePush ADDRESS_DEBUG)
{ 
    pTmgrGlobal->unTaintMemory<len>(stackAddressBeforePush - (len >> 3));

    TaintManager_Thread *pTmgrTls = static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid));    
   
     // ajustement du marquage du REGISTRE ESP/RSP, dans le cas où il est marqué
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
        // nouvel objet = ESP - (longueur pushée)
        pTmgrTls->updateTaintRegister<64>(REG_RSP, std::make_shared<TaintQword>(X_SUB, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(REG_ESP, stackAddressBeforePush)),
            ObjectSource(64, len >> 3)));
    }
#endif
} // sPUSH_I