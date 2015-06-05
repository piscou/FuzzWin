#pragma once

#include "TranslateIR.h"

class TranslateToSMTLIB : public TranslateIR
{
private:
    // BSR/BSF : booléen pour indiquer que les éléments 'De Bruijn' ont été déclarés
    bool _isDeBruijnDeclared;
 
    // renvoie la déclaration SMTLIB du tableau De Bruijn (utilisé pour BSR/BSF)
    // et met le booléen "isDeBruijnDeclared" à true
    std::string getDeBruijnArray();

    /****************************************/
    /** IMPLEMENTATION METHODES VIRTUELLES **/
    /****************************************/

protected:
    // affectation d'un nom de variable à un objet
    std::string setObjectName(const TaintPtr &tPtr);
    
    // récupère le nom de l'objet source 'objSrc'
    // => soit le numéro de variable, soit une valeur numérique
    std::string getSourceName(const ObjectSource &objSrc) const;

    /*** CONTRAINTES : PREDICAT ***/

    // déclaration de l'entête d'une nouvelle contrainte sur un predicat
    std::string getConstraintPredicateHeader(ADDRINT insAddress, PREDICATE p) const;
    // renvoie la traduction du prédicat fourni en argument
    std::string getPredicateTranslation
        (TaintManager_Thread *pTmgrTls, PREDICATE pred, ADDRINT flagsOrRegValue);
    // déclaration du 'final' d'une contrainte sur un predicat
    std::string getConstraintPredicateFooter(bool taken) const;

    /*** CONTRAINTES : DIVISEUR NUL ***/

    // déclaration de l'entête d'une nouvelle contrainte pour un diviseur nul
    std::string getConstraintNullDivisorHeader(ADDRINT insAddress) const;
    // renvoie la traduction de la formule imposant un diviseur nul
    std::string getNullDivisorTranslation(const TaintPtr &divisorPtr);
    // déclaration du 'final' d'une contrainte pour un diviseur nul
    std::string getConstraintNullDivisorFooter() const;

    /*** CONTRAINTES : QUOTIENT DIVISION HORS BORNES ***/

    // déclaration de l'entête d'une nouvelle contrainte sur le résultat d'une division
    std::string getConstraintDivOverflowHeader(bool isSignedDivision, ADDRINT insAddress) const;
    // renvoie la traduction de la formule sur le résultat d'une division
    std::string getDivOverflowTranslation(bool isSignedDivision, const TaintPtr &quotientPtr);
    // déclaration du 'final' d'une contrainte sur le résultat d'une division
    std::string getConstraintDivOverflowFooter() const;

    /*** CONTRAINTES : BOUCLES (LOOP/LOOPE/LOOPNE) ***/

    // déclaration de l'entête d'une nouvelle contrainte pour un diviseur nul
    std::string getConstraintLoopHeader(ADDRINT insAddress) const;
    // renvoie la traduction de la formule relatif à une boucle Loop (LOOP)
    std::string getLoopTranslation(const TaintPtr &regCounterPtr); 
    // renvoie la traduction de la formule relatif à une boucle Loop (LOOPE/LOOPNE)
    std::string getLoopTranslation(PREDICATE pred, const ObjectSource &objRegCounter, const ObjectSource &objZF);
    // déclaration du 'final' d'une contrainte sur le résultat d'une division
    std::string getConstraintLoopFooter() const;

    /*** CONTRAINTES : ADRESSES EFFECTIVES ***/

    // déclaration de l'entête d'une nouvelle contrainte sur une addresse
    std::string getConstraintAddressHeader(ADDRINT insAddress) const;
    // renvoie la traduction de la formule sur la valeur d'une adresse
    std::string getConstraintAddressTranslation(const TaintPtr &addrPtr, ADDRINT addrValue); 
    // déclaration du 'final' d'une contrainte sur une adresse
    std::string getConstraintAddressFooter() const;

    /***********************************/
    /** TRADUCTION DE CHAQUE RELATION **/
    /***********************************/

    // entete de la déclaration pour une instruction : "(define-fun XX () (BitVec nb) ("
    void declareRelationHeader(const TaintPtr &tPtr);
    // fin de la déclaration : "));" + infos du mode verbeux si présent
    void declareRelationFooter(const TaintPtr &tPtr);

    void translate_BYTESOURCE(const TaintPtr &tPtr);
    void translate_EXTRACT(const TaintPtr &tPtr);
    void translate_CONCAT(const TaintPtr &tPtr);

    // instructions

    void translate_X_ASSIGN(const TaintPtr &tPtr);
    void translate_X_SIGNEXTEND(const TaintPtr &tPtr);
    void translate_X_ZEROEXTEND(const TaintPtr &tPtr);
    void translate_X_ADD(const TaintPtr &tPtr);
    void translate_X_INC(const TaintPtr &tPtr);
    void translate_X_SUB(const TaintPtr &tPtr);
    void translate_X_DEC(const TaintPtr &tPtr);
    void translate_X_NEG(const TaintPtr &tPtr);
    void translate_X_MUL(const TaintPtr &tPtr);
    void translate_X_IMUL(const TaintPtr &tPtr);
    void translate_X_DIV_QUO(const TaintPtr &tPtr);
    void translate_X_DIV_REM(const TaintPtr &tPtr);
    void translate_X_IDIV_QUO(const TaintPtr &tPtr);
    void translate_X_IDIV_REM(const TaintPtr &tPtr);
    void translate_X_AND(const TaintPtr &tPtr);
    void translate_X_OR(const TaintPtr &tPtr);
    void translate_X_XOR(const TaintPtr &tPtr);
    void translate_X_NOT(const TaintPtr &tPtr);
    void translate_X_SHL(const TaintPtr &tPtr);
    void translate_X_SHR(const TaintPtr &tPtr);
    void translate_X_SAR(const TaintPtr &tPtr);
    void translate_X_ROR(const TaintPtr &tPtr);
    void translate_X_ROL(const TaintPtr &tPtr);
    void translate_X_RCR(const TaintPtr &tPtr);
    void translate_X_RCL(const TaintPtr &tPtr);
    void translate_X_SETCC(const TaintPtr &tPtr);
    void translate_X_COMPLEMENT_BIT(const TaintPtr &tPtr);
    void translate_X_SET_BIT(const TaintPtr &tPtr);
    void translate_X_CLEAR_BIT(const TaintPtr &tPtr);
    void translate_X_BSF(const TaintPtr &tPtr);
    void translate_X_BSR(const TaintPtr &tPtr);

    void translate_X_AAA_AL(const TaintPtr &tPtr);
    void translate_X_AAA_AH(const TaintPtr &tPtr);
    void translate_X_AAD(const TaintPtr &tPtr);
    void translate_X_AAM_AL(const TaintPtr &tPtr);
    void translate_X_AAM_AH(const TaintPtr &tPtr);
    void translate_X_AAS_AL(const TaintPtr &tPtr);
    void translate_X_AAS_AH(const TaintPtr &tPtr);
    void translate_X_DAA_1ST(const TaintPtr &tPtr);
    void translate_X_DAA_2ND(const TaintPtr &tPtr);
    void translate_X_DAS_1ST(const TaintPtr &tPtr);
    void translate_X_DAS_2ND(const TaintPtr &tPtr);
    void translate_X_SALC(const TaintPtr &tPtr);

    // flags

    void translate_F_LSB(const TaintPtr &tPtr);
    void translate_F_MSB(const TaintPtr &tPtr);

    void translate_F_CARRY_ADD(const TaintPtr &tPtr);
    void translate_F_CARRY_SUB(const TaintPtr &tPtr);
    void translate_F_CARRY_NEG(const TaintPtr &tPtr);
    void translate_F_CARRY_MUL(const TaintPtr &tPtr);
    void translate_F_CARRY_IMUL(const TaintPtr &tPtr);
    void translate_F_CARRY_SHL(const TaintPtr &tPtr);
    void translate_F_CARRY_SHR(const TaintPtr &tPtr); // SAR = idem
    void translate_F_CARRY_RCL(const TaintPtr &tPtr);
    void translate_F_CARRY_RCR(const TaintPtr &tPtr);
    void translate_F_CARRY_BITBYTE(const TaintPtr &tPtr);
    
    void translate_F_PARITY(const TaintPtr &tPtr);
    
    void translate_F_IS_NULL(const TaintPtr &tPtr);
    void translate_F_ARE_EQUAL(const TaintPtr &tPtr);
    void translate_F_CMPXCHG_8B16B(const TaintPtr &tPtr);

    void translate_F_OVERFLOW_ADD(const TaintPtr &tPtr);
    void translate_F_OVERFLOW_SUB(const TaintPtr &tPtr);
    void translate_F_OVERFLOW_INC(const TaintPtr &tPtr);
    void translate_F_OVERFLOW_DEC(const TaintPtr &tPtr); // NEG = idem
    void translate_F_OVERFLOW_SHL(const TaintPtr &tPtr);
    void translate_F_OVERFLOW_SHRD(const TaintPtr &tPtr);
    void translate_F_OVERFLOW_ROL(const TaintPtr &tPtr); 
    void translate_F_OVERFLOW_ROR(const TaintPtr &tPtr); 

    void translate_F_AUXILIARY_ADD(const TaintPtr &tPtr);
    void translate_F_AUXILIARY_NEG(const TaintPtr &tPtr);
    void translate_F_AUXILIARY_SUB(const TaintPtr &tPtr);
    void translate_F_AUXILIARY_INC(const TaintPtr &tPtr);
    void translate_F_AUXILIARY_DEC(const TaintPtr &tPtr);

    void translate_F_AAA(const TaintPtr &tPtr);
    void translate_F_CARRY_DAA_DAS(const TaintPtr &tPtr);
    
public:
    TranslateToSMTLIB();

    // fabrication de la formule finale, et envoi dans le pipe
    void final();
};

// Seule représentation intermédiaire utilisée actuellement : SMTLIB
typedef TranslateToSMTLIB SolverFormula;

// pointeur global vers classe de gestion de la traduction SMT-LIB
extern TranslateIR *g_pFormula;