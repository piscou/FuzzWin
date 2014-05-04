#include "decimal.h"

// CALLBACKS

void DECIMAL::cAAA(INS &ins)
{
    // AAA : ASCII Adjust After Addition. Juste besoin de la valeur des flags (pour AF) et de AL
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAA,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cAAA

void DECIMAL::cAAD(INS &ins)
{
    // AAD : ASCII Adjust AX Before Division
    // besoin de la valeur d'AX et de la base de calcul (base 10 par defaut)
    UINT32 baseValue = static_cast<UINT32>(INS_OperandImmediate(ins, 0));

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAD,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AX,
        IARG_UINT32,    baseValue,
        IARG_INST_PTR, IARG_END);
} // cAAD

void DECIMAL::cAAM(INS &ins)
{
    // AAM : ASCII Adjust AX After Multiply
    // juste besoin de la base de calcul (base 10 par defaut)
    UINT32 baseValue = static_cast<UINT32>(INS_OperandImmediate(ins, 0));

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAM,
        IARG_THREAD_ID,
        IARG_UINT32,    baseValue,
        IARG_INST_PTR, IARG_END);
} // cAAM

void DECIMAL::cAAS(INS &ins)
{
    // AAS : ASCII Adjust AL After Substraction
    // besoin d'AX et des flags (pour AF)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sAAS,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AX,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cAAS

void DECIMAL::cDAA(INS &ins)
{
    // DAA : Decimal Adjust AL After Addition
    // besoin de la valeur d'AL et des flags (Carry et Aux)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sDAA,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cDAA

void DECIMAL::cDAS(INS &ins)
{
    // DAS : Decimal Adjust AL After Subbstraction
    // besoin de la valeur d'AL et des flags (Carry et Aux)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sDAS,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_AL,
        IARG_REG_VALUE, REG_GFLAGS,
        IARG_INST_PTR, IARG_END);
} // cDAS

// SIMULATE

void DECIMAL::sAAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress)
{
   /* Manuel Intel:
    *    IF (((AL and 0FH) > 9) or (AF=1)
    *    THEN   AL <- AL+6 ; AH <- AH+1 ; CF <- 1 ; AF <- 1 ; AL <- AL and 0Fh 
    *    ELSE   CF <- 0 ; AF <- 0 ; AL <- AL and 0Fh   
    *   The OF, SF, ZF, and PF flags are undefined.*/
    
    // représentation des opérandes de destination par une relation pour chaque partie:
    // X_AAA_AL, X_AAA_AH et F_AAA (commun AF et CF)
    // le calcul de la condition se fera dans la traduction en IR

    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isRegAHTainted  = pTmgrTls->isRegisterTainted<8>(REG_AH);
    bool isAFTainted     = pTmgrTls->isAuxiliaryFlagTainted();
    UINT32 AFValue       = EXTRACTBIT(flagsValue, AUXILIARY_FLAG);

    pTmgrTls->unTaintOverflowFlag();
    pTmgrTls->unTaintParityFlag();
    pTmgrTls->unTaintSignFlag();
    pTmgrTls->unTaintZeroFlag();

    // condition du test non marquée
    if (!(isRegALTainted || isAFTainted))
    {
        // CF : démarquage (AL et AH le sont déjà)
        pTmgrTls->unTaintCarryFlag();

        // AH : s'il est marqué et que condition vraie, équivalent à un INC AH
        // sinon AH est inchangé
        if (isRegAHTainted)
        {
            if (((regALValue & 0xf) > 9) || (AFValue == 1))
            {
                ObjectSource objAH(pTmgrTls->getRegisterTaint(REG_AH)); // forcément marqué
                pTmgrTls->updateTaintRegister<8>(REG_AH, std::make_shared<TaintByte>(X_INC, objAH));
            }
        }
    }
    else
    {
        ObjectSource objAL = isRegALTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AL)))
            : std::move(ObjectSource(8, regALValue));
        ObjectSource objAF = isAFTainted
            ? std::move(ObjectSource(pTmgrTls->getTaintAuxiliaryFlag()))
            : std::move(ObjectSource(1, AFValue));

        // marquage de AL, AH et des flags : ceux-ci dépendent de la condition marquée de AAA
        pTmgrTls->updateTaintRegister<8>(REG_AL, std::make_shared<TaintByte>(X_AAA_AL, objAL, objAF));
        pTmgrTls->updateTaintRegister<8>(REG_AH, std::make_shared<TaintByte>(X_AAA_AH, objAL, objAF));
        
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_AAA, objAL, objAF));
        pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AAA, objAL, objAF));
    }
} // sAAA

void DECIMAL::sAAD(THREADID tid, ADDRINT regAXValue, ADDRINT immValue, ADDRINT insAddress)
{
    /* Manuel Intel:
    tempAL ← AL;
    tempAH ← AH;
    AL ← (tempAL + (tempAH ∗ imm8)) AND FFH;
    (* imm8 is set to 0AH for the AAD mnemonic.*)
    AH ← 0; 
    The SF, ZF, and PF flags are set according to the resulting binary
    value in the AL register; the OF, AF, and CF flags are undefined.*/
    
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);
    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isRegAHTainted  = pTmgrTls->isRegisterTainted<8>(REG_AH);

    // démarquage OF/AF/CF quoi qu'il arrive
    pTmgrTls->unTaintCarryFlag();
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintOverflowFlag();

    // marquage AL et flags ZF/PF/SF : traitement ssi AL ou AH est marqué
    if (isRegALTainted || isRegAHTainted)
    {
        ObjectSource objAL = isRegALTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AL)))
            : std::move(ObjectSource(8, EXTRACTBYTE(regAXValue, 0)));

        ObjectSource objAH = isRegAHTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AH)))
            : std::move(ObjectSource(8, EXTRACTBYTE(regAXValue, 1)));

        // démarquage AH (valant 0 quoi qu'il arrive)
        pTmgrTls->unTaintRegister<8>(REG_AH);

        // marquage AL et flags ZF/PF/SF avec le résultat
        TaintBytePtr regALafterPtr = std::make_shared<TaintByte>(
            X_AAD, objAL, objAH, ObjectSource(8, immValue));
        ObjectSource objRegALafter(regALafterPtr);

        pTmgrTls->updateTaintRegister<8>(REG_AL, regALafterPtr);
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objRegALafter));
        pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objRegALafter));
        pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objRegALafter));
    }
    // sinon démarquage ZF/PF/SF (AH et AL déjà non marqués)
    else
    {
        pTmgrTls->unTaintZeroFlag();
        pTmgrTls->unTaintSignFlag();
        pTmgrTls->unTaintParityFlag();
    }
} // sAAD

void DECIMAL::sAAM(THREADID tid, ADDRINT immValue, ADDRINT insAddress)
{
    /* Manuel Intel:
    tempAL ← AL;
    AH ← tempAL / imm8; (* imm8 is set to 0AH for the AAM mnemonic *)
    AL ← tempAL MOD imm8; 
    The SF, ZF, and PF flags are set according to the resulting binary
    value in the AL register; the OF, AF, and CF flags are undefined.*/
    
    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);
    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);

    // démarquage OF/AF/CF quoi qu'il arrive
    pTmgrTls->unTaintCarryFlag();
    pTmgrTls->unTaintAuxiliaryFlag();
    pTmgrTls->unTaintOverflowFlag();

    // marquage AL, AH et flags ZF/PF/SF : traitement ssi AL est marqué
    if (isRegALTainted)
    {
        ObjectSource objAL(pTmgrTls->getRegisterTaint(REG_AL));
        ObjectSource objBase(8, immValue);

        // marquage AH 
        pTmgrTls->updateTaintRegister<8>(REG_AH, std::make_shared<TaintByte>(X_AAM_AH, objAL, objBase));
        
        // marquage AL et flags ZF/PF/SF avec le résultat
        TaintBytePtr regALafterPtr = std::make_shared<TaintByte>(X_AAM_AL, objAL, objBase);
        ObjectSource objRegALafter(regALafterPtr);

        pTmgrTls->updateTaintRegister<8>(REG_AL, regALafterPtr);
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>(F_IS_NULL, objRegALafter));
        pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>(F_MSB, objRegALafter));
        pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY, objRegALafter));
    }
    // sinon démarquage ZF/PF/SF (AH et AL déjà non marqués)
    else
    {
        pTmgrTls->unTaintZeroFlag();
        pTmgrTls->unTaintSignFlag();
        pTmgrTls->unTaintParityFlag();
    }
} // sAAM

void DECIMAL::sAAS(THREADID tid, ADDRINT regAXValue, ADDRINT flagsValue, ADDRINT insAddress)
{
    /* Manuel Intel:
    *    IF (((AL and 0FH) > 9) or (AF=1)
    *    THEN   AX <- AX - 6 ; AH <- AH - 1 ; CF <- 1 ; AF <- 1 ; AL <- AL and 0Fh 
    *    ELSE   CF <- 0 ; AF <- 0 ; AL <- AL and 0Fh   
    *   The OF, SF, ZF, and PF flags are undefined.*/
    
    // représentation des opérandes de destination par une relation pour chaque partie:
    // X_AAS_AH, X_AAS et F_AAS (identique à F_AAA)
    // le calcul de la condition se fera dans la traduction en IR

    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isRegAHTainted  = pTmgrTls->isRegisterTainted<8>(REG_AH);
    bool isAFTainted     = pTmgrTls->isAuxiliaryFlagTainted();
    UINT32 AFValue       = EXTRACTBIT(flagsValue, AUXILIARY_FLAG);

    pTmgrTls->unTaintOverflowFlag();
    pTmgrTls->unTaintParityFlag();
    pTmgrTls->unTaintSignFlag();
    pTmgrTls->unTaintZeroFlag();

    // condition du test non marquée
    if (!(isRegALTainted || isAFTainted))
    {
        // CF => démarquage. Af déja démarqué
        pTmgrTls->unTaintCarryFlag();

        UINT32 regALValue   = EXTRACTBYTE(regAXValue, 0);
        bool conditionValue = (((regALValue & 0xf) > 9) || (AFValue == 1));     

        // si la condition est vraie et que AH est marqué, alors AX est marqué : traiter AX, AH et AL.
        // si condition fausse, ne rien faire (AL, CF et AF déja traités)
        // si AH non marqué, pareil
        if ( (conditionValue == true) && (isRegAHTainted))
        {
            // AX = AX - 6
            ObjectSource objAX(std::make_shared<TaintWord>(X_SUB, 
                ObjectSource(pTmgrTls->getRegisterTaint<16>(REG_AX, regAXValue)), 
                ObjectSource(16, 6)));

            // Extraction pour récupérer AH et AL après soustraction
            ObjectSource objExtractAL(std::make_shared<TaintByte>(EXTRACT, objAX, ObjectSource(8, 0)));
            ObjectSource objExtractAH(std::make_shared<TaintByte>(EXTRACT, objAX, ObjectSource(8, 1)));
                
            // Marquage AH apres opération AH = AH - 1
            pTmgrTls->updateTaintRegister<8>(REG_AH, 
                std::make_shared<TaintByte>(X_DEC, objExtractAH));
            // Marquage AL après opération AL = AL & 0xf
            pTmgrTls->updateTaintRegister<8>(REG_AL, 
                std::make_shared<TaintByte>(X_AND, objExtractAL, ObjectSource(8, 0xf)));
        }
    }
    else
    {
        ObjectSource objAL = isRegALTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AL)))
            : std::move(ObjectSource(8, EXTRACTBYTE(regAXValue, 0)));
        ObjectSource objAH = isRegAHTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AH)))
            : std::move(ObjectSource(8, EXTRACTBYTE(regAXValue, 1)));
        ObjectSource objAF = isAFTainted
            ? std::move(ObjectSource(pTmgrTls->getTaintAuxiliaryFlag()))
            : std::move(ObjectSource(1, AFValue));

        // marquage de AH et de AL : dépendent de la condition (AL et AF) et de AX
        pTmgrTls->updateTaintRegister<8>(REG_AL, std::make_shared<TaintByte>(X_AAS_AL, objAH, objAL, objAF));
        pTmgrTls->updateTaintRegister<8>(REG_AH, std::make_shared<TaintByte>(X_AAS_AH, objAH, objAL, objAF));
        // flags dépendant uniquement de la condition (NB idem que AAA)
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_AAA, objAL, objAF));
        pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AAA, objAL, objAF));
    }
} // sAAS

void DECIMAL::sDAA(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress)
{
    /* Manuel Intel:
    old_AL ← AL; old_CF ← CF; CF ← 0;
    IF (((AL AND 0FH) > 9) or AF = 1) THEN
        AL ← AL + 6; CF ← old_CF or (Carry from AL ← AL + 6); AF ← 1;
    ELSE
        AF ← 0;
    FI;
    IF ((old_AL > 99H) or (old_CF = 1)) THEN
        AL ← AL + 60H; CF ← 1;
    ELSE
        CF ← 0;
    FI; 
    The CF and AF flags are set if the adjustment of the value results in a decimal carry in either digit of the result.
    The SF, ZF, and PF flags are set according to the result. The OF flag is undefined.*/

    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isAFTainted     = pTmgrTls->isAuxiliaryFlagTainted();
    bool isCFTainted     = pTmgrTls->isCarryFlagTainted();
    UINT32 AFValue       = EXTRACTBIT(flagsValue, AUXILIARY_FLAG);
    UINT32 CFValue       = EXTRACTBIT(flagsValue, CARRY_FLAG);

    // marquage de AL ou sa valeur numérique à l'issue du traitement de la première condition
    TaintBytePtr regALafterFirstConditionPtr   = nullptr; 
    ADDRINT      regALValueAfterFirstCondition = regALValue;

    /** 1ERE CONDITION **/
    // cas où la première condition est non marquée
    // CF n'est pas calculé car il est redéfini dans le 2eme test
    // AF et AL sont déjà démarqués : juste ajuster la valeur numérique de AL si condition vraie
    if (!(isRegALTainted || isAFTainted))
    {
        if (((regALValue & 0xf) > 9) || (AFValue == 1)) regALValueAfterFirstCondition +=6;
    }         
    else // Si le test est marqué, alors: 
    {
        ObjectSource objAL = isRegALTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AL)))
            : std::move(ObjectSource(8, regALValue));
        ObjectSource objAF = isAFTainted
            ? std::move(ObjectSource(pTmgrTls->getTaintAuxiliaryFlag()))
            : std::move(ObjectSource(1, AFValue));

        // calcul de AF dépendant uniquement de la condition (NB : idem F_AAA)
        // on ne calcule pas CF : sera fait dans la seconde condition
        pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AAA, objAL, objAF));

        // valeur de AL après la première condition => valeur marquée
        regALafterFirstConditionPtr = std::make_shared<TaintByte>(X_DAA_1ST, objAL, objAF);
    }

    /** 2EME CONDITION **/
    // cas où la seconde condition est non marquée : 
    // 1) mise à jour du marquage de AL (il a pu être marqué lors de la première condition)
    // 3) démarquage de CF (ne rien faire car déjà non marqué)
    if (!(isRegALTainted || isCFTainted))
    {
        // test du marquage de AL lors de la première condition
        if ((bool) regALafterFirstConditionPtr)
        {
            // si condition vraie, ajuster AL = AL + 0x60 et marquer AL
            if ((regALValue > 0x99) || (CFValue == 1))
            {
                pTmgrTls->updateTaintRegister<8>(REG_AL, std::make_shared<TaintByte>(
                    X_ADD, ObjectSource(regALafterFirstConditionPtr), ObjectSource(8, 0x60)));
            }
            // si condition fausse, marquer AL avec la valeur issue de la première condition
            else pTmgrTls->updateTaintRegister<8>(REG_AL, regALafterFirstConditionPtr);
        }
    }
    // seconde condition marquée : soit AL original marqué, soit CF marqué
    else
    {
        // AL original (pour calcul de la condition)
        ObjectSource objAL = isRegALTainted
            ? ObjectSource(pTmgrTls->getRegisterTaint(REG_AL))
            : ObjectSource(8, regALValue);
        // AL après la première condition : valeur marquée ou valeur numérique
        ObjectSource objALafterFirstCondition = (bool) regALafterFirstConditionPtr
            ? ObjectSource(regALafterFirstConditionPtr)
            : ObjectSource(8, regALValueAfterFirstCondition);
        ObjectSource objCF = isCFTainted
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, CFValue);

        // marquage AL et CF selon la condition
        pTmgrTls->updateTaintRegister<8>(REG_AL, 
            std::make_shared<TaintByte>(X_DAA_2ND, objAL, objCF, objALafterFirstCondition));
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_CARRY_DAA_DAS, objAL, objCF));
    }    

    /** MARQUAGE FLAGS **/
    // démarquage OF quoi qu'il arrive
    pTmgrTls->unTaintOverflowFlag();
    // marquage ZF/SF/PF avec le résultat de AL, s'il a été marqué suite à DAA, sinon démarquage
    if (pTmgrTls->isRegisterTainted<8>(REG_AL))
    {
        ObjectSource objALafterDAA(pTmgrTls->getRegisterTaint(REG_AL));
        pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objALafterDAA));
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>  (F_IS_NULL, objALafterDAA));
        pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>  (F_MSB,     objALafterDAA));
    }
    else
    {
        pTmgrTls->unTaintParityFlag();
        pTmgrTls->unTaintZeroFlag();
        pTmgrTls->unTaintSignFlag();
    }
} // sDAA

void DECIMAL::sDAS(THREADID tid, ADDRINT regALValue, ADDRINT flagsValue, ADDRINT insAddress)
{
    /* Manuel Intel:
    old_AL ← AL; old_CF ← CF; CF ← 0;
    IF (((AL AND 0FH) > 9) or AF = 1) THEN
        AL ← AL - 6; CF ← old_CF or (Borrow from AL ← AL - 6); AF ← 1;
    ELSE
        AF ← 0;
    FI;
    IF ((old_AL > 99H) or (old_CF = 1)) THEN
        AL ← AL - 60H; CF ← 1;
    ELSE
        CF ← 0;
    FI; 
    The CF and AF flags are set if the adjustment of the value results in a decimal borrow in either digit of the result.
    The SF, ZF, and PF flags are set according to the result. The OF flag is undefined.*/

    TaintManager_Thread* pTmgrTls = getTmgrInTls(tid);

    bool isRegALTainted  = pTmgrTls->isRegisterTainted<8>(REG_AL);
    bool isAFTainted     = pTmgrTls->isAuxiliaryFlagTainted();
    bool isCFTainted     = pTmgrTls->isCarryFlagTainted();
    UINT32 AFValue       = EXTRACTBIT(flagsValue, AUXILIARY_FLAG);
    UINT32 CFValue       = EXTRACTBIT(flagsValue, CARRY_FLAG);

    // marquage de AL ou sa valeur numérique à l'issue du traitement de la première condition
    TaintBytePtr regALafterFirstConditionPtr   = nullptr; 
    ADDRINT      regALValueAfterFirstCondition = regALValue;

    /** 1ERE CONDITION **/
    // cas où la première condition est non marquée
    // CF n'est pas calculé car il est redéfini dans le 2eme test
    // AF et AL sont déjà démarqués : juste ajuster la valeur numérique de AL si condition vraie
    if (!(isRegALTainted || isAFTainted))
    {
        if (((regALValue & 0xf) > 9) || (AFValue == 1)) regALValueAfterFirstCondition -=6;
    }         
    else // Si le test est marqué, alors: 
    {
        ObjectSource objAL = isRegALTainted
            ? std::move(ObjectSource(pTmgrTls->getRegisterTaint(REG_AL)))
            : std::move(ObjectSource(8, regALValue));
        ObjectSource objAF = isAFTainted
            ? std::move(ObjectSource(pTmgrTls->getTaintAuxiliaryFlag()))
            : std::move(ObjectSource(1, AFValue));

        // calcul de AF dépendant uniquement de la condition (NB : idem F_AAA)
        // on ne calcule pas CF : sera fait dans la seconde condition
        pTmgrTls->updateTaintAuxiliaryFlag(std::make_shared<TaintBit>(F_AAA, objAL, objAF));

        // valeur de AL après la première condition => valeur marquée
        regALafterFirstConditionPtr = std::make_shared<TaintByte>(X_DAS_1ST, objAL, objAF);
    }

    /** 2EME CONDITION **/
    // cas où la seconde condition est non marquée : 
    // 1) mise à jour du marquage de AL (il a pu être marqué lors de la première condition)
    // 3) démarquage de CF (ne rien faire car déjà non marqué)
    if (!(isRegALTainted || isCFTainted))
    {
        // test du marquage de AL lors de la première condition
        if ((bool) regALafterFirstConditionPtr)
        {
            // si condition vraie, ajuster AL = AL - 0x60 et marquer AL
            if ((regALValue > 0x99) || (CFValue == 1))
            {
                pTmgrTls->updateTaintRegister<8>(REG_AL, std::make_shared<TaintByte>(
                    X_SUB, ObjectSource(regALafterFirstConditionPtr), ObjectSource(8, 0x60)));
            }
            // si condition fausse, marquer AL avec la valeur issue de la première condition
            else pTmgrTls->updateTaintRegister<8>(REG_AL, regALafterFirstConditionPtr);
        }
    }
    // seconde condition marquée : soit AL original marqué, soit CF marqué
    else
    {
        // AL original (pour calcul de la condition)
        ObjectSource objAL = isRegALTainted
            ? ObjectSource(pTmgrTls->getRegisterTaint(REG_AL))
            : ObjectSource(8, regALValue);
        // AL après la première condition : valeur marquée ou valeur numérique
        ObjectSource objALafterFirstCondition = (bool) regALafterFirstConditionPtr
            ? ObjectSource(regALafterFirstConditionPtr)
            : ObjectSource(8, regALValueAfterFirstCondition);
        ObjectSource objCF = isCFTainted
            ? ObjectSource(pTmgrTls->getTaintCarryFlag())
            : ObjectSource(1, CFValue);

        // marquage AL et CF selon la condition
        pTmgrTls->updateTaintRegister<8>(REG_AL, 
            std::make_shared<TaintByte>(X_DAS_2ND, objAL, objCF, objALafterFirstCondition));
        pTmgrTls->updateTaintCarryFlag(std::make_shared<TaintBit>(F_CARRY_DAA_DAS, objAL, objCF));
    }    

    /** MARQUAGE FLAGS **/
    // démarquage OF quoi qu'il arrive
    pTmgrTls->unTaintOverflowFlag();
    // marquage ZF/SF/PF avec le résultat de AL, s'il a été marqué suite à DAA, sinon démarquage
    if (pTmgrTls->isRegisterTainted<8>(REG_AL))
    {
        ObjectSource objALafterDAS(pTmgrTls->getRegisterTaint(REG_AL));
        pTmgrTls->updateTaintParityFlag(std::make_shared<TaintBit>(F_PARITY,  objALafterDAS));
        pTmgrTls->updateTaintZeroFlag(std::make_shared<TaintBit>  (F_IS_NULL, objALafterDAS));
        pTmgrTls->updateTaintSignFlag(std::make_shared<TaintBit>  (F_MSB,     objALafterDAS));
    }
    else
    {
        pTmgrTls->unTaintParityFlag();
        pTmgrTls->unTaintZeroFlag();
        pTmgrTls->unTaintSignFlag();
    }
} // sDAS