#pragma once

#include <TaintEngine\TaintManager.h>
#include <sstream>
#include <iostream> // cout (mode nopipe)

// entete de déclaration d'une relation
#define BEGIN_RELATION_DECLARATION  this->declareRelationHeader(tPtr)
// fin de déclaration d'une relation
#define END_RELATION_DECLARATION    this->declareRelationFooter(tPtr)

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

// constantes pour les instructions BSF/BSR
// source : Chess Programming Wiki
// pour BSF : http://chessprogramming.wikispaces.com/BitScan#Bitscan%20forward-De%20Bruijn%20Multiplication-With%20separated%20LS1B
// pour BSR : http://chessprogramming.wikispaces.com/BitScan#Bitscan%20reverse-De%20Bruijn%20Multiplication

/**** table De Bruijn ****/
static const int index64[64] = 
{
    0, 47,  1, 56, 48, 27,  2, 60,
   57, 49, 41, 37, 28, 16,  3, 61,
   54, 58, 35, 52, 50, 42, 21, 44,
   38, 32, 29, 23, 17, 11,  4, 62,
   46, 55, 26, 59, 40, 36, 15, 53,
   34, 51, 20, 43, 31, 22, 10, 45,
   25, 39, 14, 33, 19, 30,  9, 24,
   13, 18,  8, 12,  7,  6,  5, 63
}; 

/**** constante associée à cette table ****/
static const UINT64 debruijn64 = 0x03f79d71b4cb0a89;


class TranslateIR
{
private:
	// BSR/BSF : booléen pour indiquer que les éléments 'De Bruijn' ont été déclarés
	bool _isDeBruijnDeclared;

	// renvoie la déclaration SMTLIB du tableau De Bruijn (utilisé pour BSR/BSF)
	// et met le booléen "isDeBruijnDeclared" à true
	std::string getDeBruijnArray();

protected:
    std::ostringstream _formula;

    // index pour les contraintes
    UINT32 _iAssert; 

    // index pour les variables de 1/8/16/32/64/128 bits
    UINT32 _iTbit, _iTb, _iTw, _iTdw, _iTqw, _iTdqw;

    /**************/
    /** METHODES **/
    /**************/

    // déclaration d'un objet (récursif)
    void declareObject(const TaintPtr &tPtr);  

    // affectation d'un nom de variable à un objet (retourné également)
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
    std::string getLoopTranslation(PREDICATE pred, 
        const ObjectSource &objRegCounter, const ObjectSource &objZF);
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

	// entete et fin de déclaration de relation
	
	void declareRelationHeader(const TaintPtr &tPtr);
	void declareRelationFooter(const TaintPtr &tPtr);

	// relations "spéciales" de manipulation d'objets
    
	void translate_BYTESOURCE(const TaintPtr &tPtr);
    void translate_EXTRACT(const TaintPtr &tPtr);
    void translate_CONCAT(const TaintPtr &tPtr);

    // instructions x86-64

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
    void final();    
};

// pointeur global vers classe de gestion de la traduction SMT-LIB
extern TranslateIR *g_pFormula;