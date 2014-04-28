#pragma once

#include <TaintEngine\TaintManager.h>
#include <sstream>
#include <iostream> // cout (mode nopipe)

/**** conversion LEVEL_BASE::predicate -> string ****/
static const std::string predicateToString[PREDICATE_LAST] = 
{
    "",     // PREDICATE_ALWAYS_TRUE
    "",     // PREDICATE_INVALID
    "B",    // BELOW 
    "BE",   // BELOW_OR_EQUAL
    "L",    // LESS
    "LE",   // LESS_OR_EQUAL
    "NB",   // NOT_BELOW
    "NBE",  // NOT_BELOW_OR_EQUAL
    "NL",   // NOT_LESS
    "NLE",  // NOT_LESS_OR_EQUAL
    "NO",   // NOT_OVERFLOW
    "NP",   // NOT_PARITY
    "NS",   // NOT_SIGN
    "NZ",   // NOT_ZERO
    "O",    // OVERFLOW
    "P",    // PARITY
    "S",    // SIGN
    "Z",    // ZERO
    "CXZ",  // CX_NON_ZERO
    "ECXZ", // ECX_NON_ZERO
    "RCXZ", // RCX_NON_ZERO
    "SAVED_GCX" // SAVED_GCX_NON_ZERO
};

class TranslateToIR
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

    // déclaration de l'entête d'une nouvelle contrainte sur un predicat
    virtual std::string getConstraintHeader(ADDRINT insAddress, PREDICATE p) const = 0;

    // renvoie la traduction du prédicat fourni en argument
    virtual std::string getPredicateTranslation
        (TaintManager_Thread *pTmgrTls, PREDICATE pred, ADDRINT flagsOrRegValue) = 0;

    // déclaration du 'final' d'une contrainte sur un predicat
    virtual std::string getConstraintFooter(bool taken) const = 0;

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
public:
    TranslateToIR();
    
    // ajoute une contrainte sur un saut conditionnel (Jcc) marqué
    void addConstraintJcc(TaintManager_Thread *pTmgrTls, PREDICATE pred, 
        bool isTaken, ADDRINT insAddress, ADDRINT flagsOrRegValue = 0); 
    
    // fabrication de la formule finale, et envoi dans le pipe
    virtual void final() = 0;    
};
