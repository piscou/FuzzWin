#include "flagop.h"
#include <Translate\translate.h> // pour SALC

// CALLBACKS
void FLAGOP::cCLC_STC(INS &ins)
{
    // CLC/STC : clear/set Carry Flag : sera fait dans la fonction d'analyse
    // peu importe avant ou après l'exécution
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sCLC_STC,
        IARG_FAST_ANALYSIS_CALL,
        IARG_THREAD_ID,
        IARG_INST_PTR, IARG_END);
} // cCLC

void FLAGOP::cCMC(INS &ins)
{
    // CMC : complément Carry Flag : sera fait dans la fonction d'analyse
    // peu importe avant ou après l'exécution (on inversera le marquage pas la valeur)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sCMC,
        IARG_FAST_ANALYSIS_CALL,
        IARG_THREAD_ID,
        IARG_INST_PTR, IARG_END);
} // cCMC

void FLAGOP::cLAHF(INS &ins)
{
    // LAHF : load Status Flags into AH
    // argument nécessaire = valeur des flags
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sLAHF,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_GFLAGS, // valeur des flags (avant ou apres exécution car ils restent inchangés)
        IARG_INST_PTR, IARG_END);
} // cLAHF


void FLAGOP::cSAHF(INS &ins)
{
    // SAHF : Store AH Into Flags
    // pas besoin de la valeur de AH : soit il est marqué, soit les flags seront démarqués
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sSAHF,
        IARG_THREAD_ID,
        IARG_INST_PTR, IARG_END);
} // cSAHF

void FLAGOP::cSALC(INS &ins)
{
    // SALC : SET AL on Carry Flag:  fonction non documentée par Intel (mais pour PIN oui !!!)
    // si CF == 0 => AL = 0 ; si CF == 1 => AL = FF
    // => insertion d'une fonction d'analyse avec valeur de AL APRES exécution
    // selon sa valeur on saura si CF valait 0 ou 1 avant exécution
    // puis insertion d'une contrainte sur le CF, et démarquage AL
    // argument nécessaire = valeur des flags
    INS_InsertCall(ins, IPOINT_AFTER, (AFUNPTR) sSALC,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL, // valeur AL apres exécution (soit 0xff, soit 0)
        IARG_INST_PTR,
        IARG_END);
} // cLAHF


// SIMULATE

void PIN_FAST_ANALYSIS_CALL FLAGOP::sCLC_STC(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // simple démarquage du CF
    pTmgrTls->unTaintCarryFlag();
} // sCLC

void PIN_FAST_ANALYSIS_CALL FLAGOP::sCMC(THREADID tid, ADDRINT insAddress)
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    // simple inversion (= NOT) du CF, si marqué
    if (pTmgrTls->isCarryFlagTainted())
    {
        ObjectSource objCF(pTmgrTls->getTaintCarryFlag());
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(X_NOT, objCF));
    }
} // sCMC

void FLAGOP::sLAHF(THREADID tid, ADDRINT regFlagsValue, ADDRINT insAddress)
{
    // AH ← EFLAGS(SF:ZF:0:AF:0:PF:1:CF)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // il faut au moins l'un des flags marqués, sinon démarquage AH
    bool isTaintCF = pTmgrTls->isCarryFlagTainted();
    bool isTaintPF = pTmgrTls->isParityFlagTainted();
    bool isTaintAF = pTmgrTls->isAuxiliaryFlagTainted();
    bool isTaintZF = pTmgrTls->isZeroFlagTainted();
    bool isTaintSF = pTmgrTls->isSignFlagTainted();
    if ( ! (isTaintCF || isTaintPF || isTaintAF || isTaintZF || isTaintSF))
    {
        pTmgrTls->unTaintRegister<8>(REG_AH);
    }
    else
    {
        // construction d'un taintByte comme concaténation de bits
        TaintByte tbLahf(CONCAT);
        // Bit 0 : CF (marquage ou valeur)
        if (isTaintCF) tbLahf.addSource(pTmgrTls->getTaintCarryFlag());
        else           tbLahf.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, CARRY_FLAG));
       
        // Bit 1 : 1
        tbLahf.addConstantAsASource<1>(1);

        // Bit 2 : PF (marquage ou valeur)
        if (isTaintPF) tbLahf.addSource(pTmgrTls->getTaintParityFlag());
        else           tbLahf.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, PARITY_FLAG));
       
        // Bit 3 : 0
        tbLahf.addConstantAsASource<1>(0);

        // Bit 4 : AF (marquage ou valeur)
        if (isTaintAF) tbLahf.addSource(pTmgrTls->getTaintAuxiliaryFlag());
        else           tbLahf.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, AUXILIARY_FLAG));
       
        // Bit 5 : 0
        tbLahf.addConstantAsASource<1>(0);

        // Bit 6 : ZF (marquage ou valeur)
        if (isTaintZF) tbLahf.addSource(pTmgrTls->getTaintZeroFlag());
        else           tbLahf.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, ZERO_FLAG));
       
        // Bit 7 : SF (marquage ou valeur)
        if (isTaintSF) tbLahf.addSource(pTmgrTls->getTaintSignFlag());
        else           tbLahf.addConstantAsASource<1>(EXTRACTBIT(regFlagsValue, SIGN_FLAG));
       
        // marquage AH
        pTmgrTls->updateTaintRegister<8>(REG_AH, std::make_shared<TaintByte>(tbLahf));
    }
} // sLAHF

void FLAGOP::sSAHF(THREADID tid, ADDRINT insAddress)
{
    // EFLAGS(SF:ZF:0:AF:0:PF:1:CF) -> AH 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // si AH non marqué, démarquage des flags SZAPC
    if ( ! pTmgrTls->isRegisterTainted<8>(REG_AH))
    {
        pTmgrTls->unTaintCarryFlag();
        pTmgrTls->unTaintParityFlag();
        pTmgrTls->unTaintAuxiliaryFlag();
        pTmgrTls->unTaintZeroFlag();
        pTmgrTls->unTaintSignFlag();
    }
    else
    {
        // extraction des bits de AH pour marquage Flags
        ObjectSource objAH(pTmgrTls->getRegisterTaint(REG_AH));
        
        // Bit 0 : CF 
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(
            EXTRACT, objAH, ObjectSource(8, CARRY_FLAG)));
        // Bit 2 : PF
        pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(
            EXTRACT, objAH, ObjectSource(8, PARITY_FLAG)));
        // Bit 4 : AF
        pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(
            EXTRACT, objAH, ObjectSource(8, AUXILIARY_FLAG)));
        // Bit 6 : ZF
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(
            EXTRACT, objAH, ObjectSource(8, ZERO_FLAG)));
        // Bit 7 : SF
        pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(
            EXTRACT, objAH, ObjectSource(8, SIGN_FLAG)));
    }
} // sSAHF

void FLAGOP::sSALC(THREADID tid, ADDRINT regALValue, ADDRINT insAddress)
{
#if 0
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    // insertion de la contrainte, si CF était marqué
    if (pTmgrTls->isCarryFlagTainted()) 
    {
        _LOGTAINT(tid, insAddress, "SALC");
        
        // test de la valeur d'AH pour en déduire la valeur de CF avant
        bool valueCF = (regALValue == 0) ? false : true;
        g_pFormula->addConstraint_BELOW(pTmgrTls, insAddress, valueCF);
    }

    // quoiqu'il arrive, démarquage AL qui est une valeur fixe
    // la contrainte sur sa valeur a été exprimée via CF
    // cf comportement identique que SETcc
    pTmgrTls->unTaintRegister<8>(REG_AL);
#endif
} // sSALC
