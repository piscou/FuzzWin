#pragma once

#include "TaintManager.h"
#include <sstream>
#if DEBUG
#include <iostream> // cout
#endif

// constantes pour les instructions BSF/BSR
// source : Chess Programming Wiki
// pour BSF : http://chessprogramming.wikispaces.com/BitScan#Bitscan%20forward-De%20Bruijn%20Multiplication-With%20separated%20LS1B
// pour BSR : http://chessprogramming.wikispaces.com/BitScan#Bitscan%20reverse-De%20Bruijn%20Multiplication

/**** table De Bruijn ****/
static const int index64[64] = {
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

/***  BSF  ***/
/* int bitScanForward(U64 bb) 
{
    assert (bb != 0);
    return index64[((bb ^ (bb-1)) * debruijn64) >> 58];
} */

/***  BSR  ***/
/* int bitScanReverse(U64 bb) {
   assert (bb != 0);
   bb |= bb >> 1; 
   bb |= bb >> 2;
   bb |= bb >> 4;
   bb |= bb >> 8;
   bb |= bb >> 16;
   bb |= bb >> 32;
   return index64[(bb * debruijn64) >> 58];
} */

class SolverFormula
{
private:
    std::ostringstream _formula;

    // index pour les contraintes
    UINT32 _iAssert; 

    // index pour les variables de 1/8/16/32/64/128 bits
    UINT32 _iTbit, _iTb, _iTw, _iTdw, _iTqw, _iTdqw;

    // booléen pour indiquer que le tableau De Bruijn et la constante associée
    // ont été déclarés
    bool _isDeBruijnDeclared;

    // procédure de déclaration d'un objet (récursif)
    void declareObject(const TaintPtr &tPtr);  

    // procedure de declaration d'une relation entre un objet et ses sources
    void declareRelation(const TaintPtr &tPtr, const vector<ObjectSource> &sources);

    // insertion dans la formule de l'entête d'une nouvelle contrainte
    // ie n° de contrainte, addresse, et type de condition (si mode DEBUG)
    void declareConstraintHeader(ADDRINT insAddress, PREDICATE p);

    // insertion dans la formule du final d'une nouvelle contrainte
    // ie la commande "assert" puis true ou false selon branche prise ou non
    void declareConstraintFooter(const std::string &number, bool taken);

    // insere dans la formule le nom de l'objet 'objSrc'
    // => soit le numéro de variable, soit une valeur numérique
    // si précisé, insère un espace à la fin
    static void insertSourceName(std::string &out, const ObjectSource &objSrc);

public:
    // renvoie la déclaration SMTLIB du tableau De Bruijn (utilisé pour BSR/BSF)
    // et met le booléen "isDeBruijnDeclared" à true
    // NB : le tableau est une liste de 64 valeurs sur 64bits
    // qq soit la taille utilisée dans BSF/BSR : il faudra 
    // faire un zero_extend de la source scannée
    // ********* A PASSER EN PRIVATE EN VERSION DEFINITIVE ********
    std::string getDeBruijnArray();

    SolverFormula();

    // traduit une contrainte dépendant des flags 
    void addConstraint_OVERFLOW (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken);
    void addConstraint_PARITY   (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken);
    void addConstraint_SIGN     (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken);
    void addConstraint_ZERO     (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken);
    void addConstraint_BELOW    (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken);
    void addConstraint_LESS          (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken, ADDRINT flagsValue);
    void addConstraint_LESS_OR_EQUAL (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken, ADDRINT flagsValue);
    void addConstraint_BELOW_OR_EQUAL(TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken, ADDRINT flagsValue);

    // fabrication de la formule finale, et envoi dans le pipe
    void final();
};

// pointeur global vers classe de gestion de la traduction SMT-LIB
extern SolverFormula *g_pFormula;