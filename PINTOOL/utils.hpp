// démarquage rapide registre par callback 
template<UINT32 len> void PIN_FAST_ANALYSIS_CALL UTILS::uREG(THREADID tid, REG reg)
{  
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    pTmgrTls->unTaintRegister<len>(reg); 
}