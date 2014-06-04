#pragma once

#include <TaintEngine\TaintManager.h>
#include <sstream>
#include <iostream> // cout (mode nopipe)

class TranslateIR
{
protected:
    std::ostringstream _formula;

    // index pour les contraintes
    UINT32 _iAssert; 

    // index pour les variables de 1/8/16/32/64/128 bits
    UINT32 _iTbit, _iTb, _iTw, _iTdw, _iTqw, _iTdqw;

    /*********************/
    /** METHODE COMMUNE **/
    /*********************/

    // déclaration d'un objet (récursif)
    void declareObject(const TaintPtr &tPtr);  

    /*******************************/
    /** METHODES VIRTUELLES PURES **/
    /*******************************/

    // affectation d'un nom de variable à un objet (retourné également)
    virtual std::string setObjectName(const TaintPtr &tPtr) = 0;

    // récupère le nom de l'objet source 'objSrc'
    // => soit le numéro de variable, soit une valeur numérique
    virtual std::string getSourceName(const ObjectSource &objSrc) const = 0;

    /*** CONTRAINTES : PREDICAT ***/

    // déclaration de l'entête d'une nouvelle contrainte sur un predicat
    virtual std::string getConstraintPredicateHeader(ADDRINT insAddress, PREDICATE p) const = 0;
    // renvoie la traduction du prédicat fourni en argument
    virtual std::string getPredicateTranslation
        (TaintManager_Thread *pTmgrTls, PREDICATE pred, ADDRINT flagsOrRegValue) = 0;
    // déclaration du 'final' d'une contrainte sur un predicat
    virtual std::string getConstraintPredicateFooter(bool taken) const = 0;

    /*** CONTRAINTES : DIVISEUR NUL ***/

    // déclaration de l'entête d'une nouvelle contrainte pour un diviseur nul
    virtual std::string getConstraintNullDivisorHeader(ADDRINT insAddress) const = 0;
    // renvoie la traduction de la formule imposant un diviseur nul
    virtual std::string getNullDivisorTranslation(const TaintPtr &divisorPtr) = 0;
    // déclaration du 'final' d'une contrainte pour un diviseur nul
    virtual std::string getConstraintNullDivisorFooter() const = 0;

    /*** CONTRAINTES : QUOTIENT DIVISION HORS BORNES ***/

    // déclaration de l'entête d'une nouvelle contrainte sur le résultat d'une division
    virtual std::string getConstraintDivOverflowHeader(bool isSignedDivision, ADDRINT insAddress) const = 0;
    // renvoie la traduction de la formule sur le résultat d'une division
    virtual std::string getDivOverflowTranslation(bool isSignedDivision, const TaintPtr &quotientPtr) = 0;
    // déclaration du 'final' d'une contrainte sur le résultat d'une division
    virtual std::string getConstraintDivOverflowFooter() const = 0;

    /*** CONTRAINTES : BOUCLES (LOOP/LOOPE/LOOPNE) ***/

    // déclaration de l'entête d'une nouvelle contrainte pour un diviseur nul
    virtual std::string getConstraintLoopHeader(ADDRINT insAddress) const = 0;
    // renvoie la traduction de la formule relatif à une boucle Loop (LOOP)
    virtual std::string getLoopTranslation(const TaintPtr &regCounterPtr) = 0; 
    // renvoie la traduction de la formule relatif à une boucle Loop (LOOPE/LOOPNE)
    virtual std::string getLoopTranslation(PREDICATE pred, 
        const ObjectSource &objRegCounter, const ObjectSource &objZF) = 0;
    // déclaration du 'final' d'une contrainte sur le résultat d'une division
    virtual std::string getConstraintLoopFooter() const = 0;

    /*** CONTRAINTES : ADRESSES EFFECTIVES ***/

    // déclaration de l'entête d'une nouvelle contrainte sur une addresse
    virtual std::string getConstraintAddressHeader(ADDRINT insAddress) const = 0;
    // renvoie la traduction de la formule sur la valeur d'une adresse
    virtual std::string getConstraintAddressTranslation(const TaintPtr &addrPtr, ADDRINT addrValue) = 0; 
    // déclaration du 'final' d'une contrainte sur une adresse
    virtual std::string getConstraintAddressFooter() const = 0;

    /***********************************/
    /** TRADUCTION DE CHAQUE RELATION **/
    /***********************************/

    virtual void translate_BYTESOURCE(const TaintPtr &tPtr) = 0;
    virtual void translate_EXTRACT(const TaintPtr &tPtr) = 0;
    virtual void translate_CONCAT(const TaintPtr &tPtr) = 0;

    // instructions

    virtual void translate_X_ASSIGN(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SIGNEXTEND(const TaintPtr &tPtr) = 0;
    virtual void translate_X_ZEROEXTEND(const TaintPtr &tPtr) = 0;
    virtual void translate_X_ADD(const TaintPtr &tPtr) = 0;
    virtual void translate_X_INC(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SUB(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DEC(const TaintPtr &tPtr) = 0;
    virtual void translate_X_NEG(const TaintPtr &tPtr) = 0;
    virtual void translate_X_MUL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_IMUL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DIV_QUO(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DIV_REM(const TaintPtr &tPtr) = 0;
    virtual void translate_X_IDIV_QUO(const TaintPtr &tPtr) = 0;
    virtual void translate_X_IDIV_REM(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AND(const TaintPtr &tPtr) = 0;
    virtual void translate_X_OR(const TaintPtr &tPtr) = 0;
    virtual void translate_X_XOR(const TaintPtr &tPtr) = 0;
    virtual void translate_X_NOT(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SHL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SHR(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SAR(const TaintPtr &tPtr) = 0;
    virtual void translate_X_ROR(const TaintPtr &tPtr) = 0;
    virtual void translate_X_ROL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_RCR(const TaintPtr &tPtr) = 0;
    virtual void translate_X_RCL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SETCC(const TaintPtr &tPtr) = 0;
    virtual void translate_X_COMPLEMENT_BIT(const TaintPtr &tPtr) = 0;
    virtual void translate_X_SET_BIT(const TaintPtr &tPtr) = 0;
    virtual void translate_X_CLEAR_BIT(const TaintPtr &tPtr) = 0;
    virtual void translate_X_BSF(const TaintPtr &tPtr) = 0;
    virtual void translate_X_BSR(const TaintPtr &tPtr) = 0;
    
    virtual void translate_X_AAA_AL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AAA_AH(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AAD(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AAM_AL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AAM_AH(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AAS_AL(const TaintPtr &tPtr) = 0;
    virtual void translate_X_AAS_AH(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DAA_1ST(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DAA_2ND(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DAS_1ST(const TaintPtr &tPtr) = 0;
    virtual void translate_X_DAS_2ND(const TaintPtr &tPtr) = 0;

    virtual void translate_X_SALC(const TaintPtr &tPtr) = 0;
    // flags

    virtual void translate_F_LSB(const TaintPtr &tPtr) = 0;
    virtual void translate_F_MSB(const TaintPtr &tPtr) = 0;

    virtual void translate_F_CARRY_ADD(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_SUB(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_NEG(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_MUL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_IMUL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_SHL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_SHR(const TaintPtr &tPtr) = 0; // SAR = idem
    virtual void translate_F_CARRY_RCL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_RCR(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_BITBYTE(const TaintPtr &tPtr) = 0;
    
    virtual void translate_F_PARITY(const TaintPtr &tPtr) = 0;
    
    virtual void translate_F_IS_NULL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_ARE_EQUAL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CMPXCHG_8B16B(const TaintPtr &tPtr) = 0;

    virtual void translate_F_OVERFLOW_ADD(const TaintPtr &tPtr) = 0;
    virtual void translate_F_OVERFLOW_SUB(const TaintPtr &tPtr) = 0;
    virtual void translate_F_OVERFLOW_INC(const TaintPtr &tPtr) = 0;
    virtual void translate_F_OVERFLOW_DEC(const TaintPtr &tPtr) = 0; // NEG = idem
    virtual void translate_F_OVERFLOW_SHL(const TaintPtr &tPtr) = 0;
    virtual void translate_F_OVERFLOW_SHRD(const TaintPtr &tPtr) = 0;
    virtual void translate_F_OVERFLOW_ROL(const TaintPtr &tPtr) = 0; 
    virtual void translate_F_OVERFLOW_ROR(const TaintPtr &tPtr) = 0;

    virtual void translate_F_AUXILIARY_ADD(const TaintPtr &tPtr) = 0;
    virtual void translate_F_AUXILIARY_NEG(const TaintPtr &tPtr) = 0;
    virtual void translate_F_AUXILIARY_SUB(const TaintPtr &tPtr) = 0;
    virtual void translate_F_AUXILIARY_INC(const TaintPtr &tPtr) = 0;
    virtual void translate_F_AUXILIARY_DEC(const TaintPtr &tPtr) = 0;

    virtual void translate_F_AAA(const TaintPtr &tPtr) = 0;
    virtual void translate_F_CARRY_DAA_DAS(const TaintPtr &tPtr) = 0;

public:
    TranslateIR();
    
    // ajoute une contrainte sur un saut conditionnel (Jcc) marqué
    void addConstraintJcc(TaintManager_Thread *pTmgrTls, PREDICATE pred, 
        bool isTaken, ADDRINT insAddress, ADDRINT flagsOrRegValue = 0); 

    // ajoute une contrainte sur une division marquée
    void addConstraintDivision(bool isSignedDivision, const TaintPtr &quotient, ADDRINT insAddress);

    // ajoute une contrainte sur une boucle simple (LOOP)
    void addConstraintLoop(const TaintPtr &regCounterPtr, ADDRINT insAddress);
    // ajoute une contrainte sur une boucle avec test du zero flag (LOOPE / LOOPNE)
    void addConstraintLoop(PREDICATE pred, const ObjectSource &objRegCounter, 
        const ObjectSource &objZF, ADDRINT insAddress);

    // Ajout d'une contrainte sur la valeur d'une addresse
    void addConstraintAddress(const TaintPtr &addrPtr, ADDRINT addrValue, ADDRINT insAddress);
    
    // fabrication de la formule finale
    virtual void final() = 0;    
};
