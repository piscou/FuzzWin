#include "translateSMTLIB.h"

TranslateToSMTLIB::TranslateToSMTLIB()
    : TranslateToIR(), _isDeBruijnDeclared(false) {}

std::string TranslateToSMTLIB::getDeBruijnArray()
{
    // variables utilisées par les instructions BSR et BSF
    // cf. commentaires dans translate.h

    std::string result;

    // déclaration de la constante multiplicative
    result += "(define-const constante (_ BitVec 64) #x";
    result += hexstr(debruijn64, 8).substr(2); // pour éliminer le "Ox"
    result += ")\n";

    // définition du tableau debruijn64. Il se crée via une fonction:
    // paramètre 'x'    = index
    // valeur de retour = valeur du tableau
    // ALTERNATIVE A UN ARRAY CAR UN ARRAY NE PERMET PAS D'UTILISER UN '(get-model)'
    // pour obtenir les résultats !!!!!
    result += "(define-fun index64 ((x (_ BitVec 64))) (_ BitVec 64)\n";
        
    // stockage de 64 valeurs : 64x la fonction "(ite (= x (_ bvAA 64)) (_ bvVAL 64) ";
    for (UINT32 index = 0 ; index < 64 ; ++index)   
    {
        result += "  (ite (= x (_ bv" + decstr(index) + " 64)) ";
        result +=             "(_ bv" + decstr(index64[index]) + " 64)\n";
    }

    // pour le dernier ite, si non égal renvoyer 0 (comme si une erreur était arrivée)
    result +=     "  (_ bv0 64)";

    // 64 parenthèses fermantes (une par 'ite') 
    for (UINT32 index = 0 ; index < 8 ; ++index)
    {
        result += "))))))))"; // 8 parenthèses par 8
    }

    // parenthèse finale
    result += ")\n";

    // le tableau et la constante sont déclarés
    _isDeBruijnDeclared = true;

    return (result);
}

// affectation d'un nom de variable à un objet
std::string TranslateToSMTLIB::setObjectName(const TaintPtr &tPtr)
{
    // fabrication du nom de variable unique selon la taille du resultat
    std::string name;
    switch (tPtr->getLength()) 
    {
    case 1:	  name = "TBIT" + decstr(++_iTbit); break;
    case 8:	  name = "TB"   + decstr(++_iTb);   break;
    case 16:  name = "TW"   + decstr(++_iTw);   break;
    case 32:  name = "TDW"  + decstr(++_iTdw);  break;
    case 64:  name = "TQW"  + decstr(++_iTqw);  break;
    case 128: name = "TDQW" + decstr(++_iTdqw); break;
    default : name = "error"; break;
    }
    tPtr->setName(name);
    return (name); // R-VALUE
} // setObjectName

// nom de variable pour les objets, utilisées dans les formules SMTLIB
std::string TranslateToSMTLIB::getSourceName(const ObjectSource &objSrc) const
{
    // si objet marqué, retourner son nom de variable
    if (objSrc.isSrcTainted())	 return (objSrc.getTaintedSource()->getName()); 
    // sinon fabrication de la valeur, en format SMTLIB
    else 
    {
        UINT32 srcLength = objSrc.getLength(); // longueur de l'objet (en bits)
        ADDRINT value    = objSrc.getValue();  // valeur numérique représentée par l'objet
        
        // cas TaintBit : résultat décrit en binaire
        if (srcLength == 1)	  return (value ? "#b1" : "#b0");
        // dans les autres cas : resultat en hexa
        else
        {
            // la fonction StringFromAddrint (API PIN) convertit un ADDRINT 
            // en chaine de caractères. Or la source est encodée sur 'srcLength' bits
            // donc extraire les 2/4/8/16 derniers chiffres de la chaine
            std::string valueString(StringFromAddrint(value));
            return ("#x" + valueString.substr(valueString.size() - (srcLength >> 2)));       
        }
    }
} // getSourceName

////////////////////////////////////
// DECLARATION DES OBJETS MARQUES //
////////////////////////////////////

// entete de la déclaration : affectation d'un nom + '(define-fun XX () (BitVec nb) ('
void TranslateToSMTLIB::declareRelationHeader(const TaintPtr &tPtr)
{
    const std::string name = this->setObjectName(tPtr);

    // declaration de l'entête de ligne : nom de variable et longueur
    _formula << "(define-fun " << name << " () (_ BitVec " << tPtr->getLength() << ") (";
}

// fin de la déclaration : )); + infos du mode verbeux si présent
void TranslateToSMTLIB::declareRelationFooter(const TaintPtr &tPtr)
{
    _formula << "));";
    if (g_verbose)
    {
        _formula << relationStrings[tPtr->getSourceRelation()] << " / ";
        _formula << tPtr->getVerboseDetails();
    }
    _formula  << '\n';
}

/** RELATIONS **/

void TranslateToSMTLIB::translate_BYTESOURCE(const TaintPtr &tPtr)
{
    // BYTESOURCE : nom de variable spécifique
    std::string objectName("OFF" + decstr(tPtr->getSource(0).getValue()));
    tPtr->setName(objectName);

    // déclaration particulière en "declare-const", sans header ni footer
    _formula << "(declare-const " << objectName << " (_ BitVec 8))\n";
}

void TranslateToSMTLIB::translate_EXTRACT(const TaintPtr &tPtr)
{
    // EXTRACT : source0 forcément marqué, source1 (index) forcément valeur
    ObjectSource source      = tPtr->getSource(0);
    UINT32 indexOfExtraction = static_cast<UINT32>(tPtr->getSource(1).getValue());
    UINT32 lengthOfResult    = tPtr->getLength();

    // borne min = index d'extraction * longueur du resultat
    UINT32 lowerLimit = indexOfExtraction * lengthOfResult;
    // borne max = borne min + (longueur - 1)
    UINT32 higherLimit = lowerLimit + (lengthOfResult - 1);

    BEGIN_RELATION_DECLARATION;

    _formula << "(_ extract " << higherLimit << ' ' << lowerLimit << ") ";     
    // ajout de l'objet subissant l'extraction
    _formula <<  source.getTaintedSource()->getName();

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_CONCAT(const TaintPtr &tPtr)
{
    // CONCAT : concaténation des objets fournis en Sources
    // Attention : les objets seront inséres du plus fort au plus faible
    // d'ou le rbegin/rend (cf def CONCAT du langage SMTLIB)
    std::vector<ObjectSource> sources = tPtr->getSources();

    BEGIN_RELATION_DECLARATION;

    _formula << "concat";
    for (auto it = sources.rbegin();  it != sources.rend() ; ++it) 
    {
        _formula <<  ' ' << this->getSourceName(*it);
    } 

    END_RELATION_DECLARATION;
}

// instructions

void TranslateToSMTLIB::translate_X_ASSIGN(const TaintPtr &tPtr)
{
    // on affecte à l'objet le nom de la source
    // cela evite de déclarer une nouvelle variable dans le solveur 
    tPtr->setName(tPtr->getSource(0).getTaintedSource()->getName());
}

void TranslateToSMTLIB::translate_X_SIGNEXTEND(const TaintPtr &tPtr)
{
    UINT32 lengthOfResult = tPtr->getLength();
    ObjectSource source   = tPtr->getSource(0); // forcément marquée
    UINT32 lengthOfSource = source.getLength();

    BEGIN_RELATION_DECLARATION;

    _formula << "(_ sign_extend " << (lengthOfResult - lengthOfSource) << ") ";
    _formula << source.getTaintedSource()->getName();

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_ZEROEXTEND(const TaintPtr &tPtr)
{
    UINT32 lengthOfResult = tPtr->getLength();
    ObjectSource source   = tPtr->getSource(0); // forcément marquée
    UINT32 lengthOfSource = source.getLength();

    BEGIN_RELATION_DECLARATION;

    _formula << "(_ zero_extend " << (lengthOfResult - lengthOfSource) << ") ";
    _formula << source.getTaintedSource()->getName();

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_ADD(const TaintPtr &tPtr)
{
    ObjectSource src0   = tPtr->getSource(0);
    ObjectSource src1   = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvadd " << this->getSourceName(src0) << ' ' << this->getSourceName(src1);
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_INC(const TaintPtr &tPtr)
{
    // source 0 forcément marquée

    BEGIN_RELATION_DECLARATION;
    _formula << "bvadd " << tPtr->getSource(0).getTaintedSource()->getName() << " (_ bv1 " << tPtr->getLength() << ')';
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SUB(const TaintPtr &tPtr)
{
    ObjectSource src0   = tPtr->getSource(0);
    ObjectSource src1   = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvsub " << this->getSourceName(src0) << ' ' << this->getSourceName(src1);
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DEC(const TaintPtr &tPtr)
{
    // source 0 forcément marquée

    BEGIN_RELATION_DECLARATION;
    _formula << "bvsub " << tPtr->getSource(0).getTaintedSource()->getName()  << " (_ bv1 " << tPtr->getLength() << ')';
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_NEG(const TaintPtr &tPtr)
{
    // source 0 forcément marquée

    BEGIN_RELATION_DECLARATION;
    _formula << "bvneg " << tPtr->getSource(0).getTaintedSource()->getName();
    END_RELATION_DECLARATION;
}

// NON IMPLEMENTE : MUL
void TranslateToSMTLIB::translate_X_MUL(const TaintPtr &tPtr)
{
    // MUL : longueur resultat = 2*longueur des sources. Or en SMTLIB longueur resultat = longueur source
    // donc necessite de mettre les opérandes à la longueur de la destination 
    // pour MUL : on doit étendre les opérandes en zéro-extend
    const std::string zeroExtend("((_ zero_extend " + decstr(tPtr->getLength() >> 1) + ") ");
    ObjectSource src0 = tPtr->getSource(0);
    ObjectSource src1 = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvmul " << zeroExtend << this->getSourceName(src0) << ") ";
    _formula <<             zeroExtend << this->getSourceName(src1) << ')';
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_IMUL(const TaintPtr &tPtr)
{
    // IMUL : longueur resultat = 2*longueur des sources. Or en SMTLIB longueur resultat = longueur source
    // donc necessite de mettre les opérandes à la longueur de la destination 
    // pour IMUL : on doit étendre les opérandes en sign-extend
    const std::string signExtend("((_ sign_extend " + decstr(tPtr->getLength() >> 1) + ") ");
    ObjectSource src0 = tPtr->getSource(0);
    ObjectSource src1 = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvmul " << signExtend << this->getSourceName(src0) << ") ";
    _formula <<             signExtend << this->getSourceName(src1) << ')';
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DIV_QUO(const TaintPtr &tPtr)
{
    UINT32 lengthOfQuotient      = tPtr->getLength();
    ObjectSource objHighDividend = tPtr->getSource(0);
    ObjectSource objLowDividend  = tPtr->getSource(1);
    ObjectSource objDivisor      = tPtr->getSource(2);

    BEGIN_RELATION_DECLARATION;

    // taille resultat = taille diviseur = 1/2 taille dividende
    // il faut donc effectuer l'opération "Dividende / zero_extend(diviseur)" 
    // et en extraire la partie basse pour obtenir le résultat
    _formula << "(_ extract " << (lengthOfQuotient - 1) << " 0) (bvudiv ";
    
    // concaténation du dividende
    _formula << "(concat " << this->getSourceName(objHighDividend);
    _formula << ' '        << this->getSourceName(objLowDividend) << ')';       
   
    // Source2 : diviseur à étendre à la taille du dividende = ajouter 'lengthResult' zéros
    _formula << " ((_ zero_extend " << lengthOfQuotient << ") " << this->getSourceName(objDivisor) << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DIV_REM(const TaintPtr &tPtr)
{
    UINT32 lengthOfQuotient      = tPtr->getLength();
    ObjectSource objHighDividend = tPtr->getSource(0);
    ObjectSource objLowDividend  = tPtr->getSource(1);
    ObjectSource objDivisor      = tPtr->getSource(2);

    BEGIN_RELATION_DECLARATION;

    // taille resultat = taille diviseur = 1/2 taille dividende
    // il faut donc effectuer l'opération "Dividende / zero_extend(diviseur)" 
    // et en extraire la partie basse pour obtenir le résultat
    _formula << "(_ extract " << (lengthOfQuotient - 1) << " 0) (bvurem ";
    
    // concaténation du dividende
    _formula << "(concat " << this->getSourceName(objHighDividend);
    _formula << ' '        << this->getSourceName(objLowDividend) << ')';       
   
    // Source2 : diviseur à étendre à la taille du dividende = ajouter 'lengthResult' zéros
    _formula << " ((_ zero_extend " << lengthOfQuotient << ") " << this->getSourceName(objDivisor) << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_IDIV_QUO(const TaintPtr &tPtr)
{
    UINT32 lengthOfQuotient      = tPtr->getLength();
    ObjectSource objHighDividend = tPtr->getSource(0);
    ObjectSource objLowDividend  = tPtr->getSource(1);
    ObjectSource objDivisor      = tPtr->getSource(2);

    BEGIN_RELATION_DECLARATION;

    // taille resultat = taille diviseur = 1/2 taille dividende
    // il faut donc effectuer l'opération "Dividende / sign_extend(diviseur)" 
    // et en extraire la partie basse pour obtenir le résultat
    _formula << "(_ extract " << (lengthOfQuotient - 1) << " 0) (bvsdiv ";
    
    // concaténation du dividende
    _formula << "(concat " << this->getSourceName(objHighDividend);
    _formula << ' '        << this->getSourceName(objLowDividend) << ')';       
   
    // Source2 : diviseur à sign-extend à la taille du dividende
    _formula << " ((_ sign_extend " << lengthOfQuotient << ") " << this->getSourceName(objDivisor) << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_IDIV_REM(const TaintPtr &tPtr)
{
    UINT32 lengthOfQuotient      = tPtr->getLength();
    ObjectSource objHighDividend = tPtr->getSource(0);
    ObjectSource objLowDividend  = tPtr->getSource(1);
    ObjectSource objDivisor      = tPtr->getSource(2);

    BEGIN_RELATION_DECLARATION;

    // taille resultat = taille diviseur = 1/2 taille dividende
    // il faut donc effectuer l'opération "Dividende / sign_extend(diviseur)" 
    // et en extraire la partie basse pour obtenir le résultat
    _formula << "(_ extract " << (lengthOfQuotient - 1) << " 0) (bvsrem ";
    
    // concaténation du dividende
    _formula << "(concat " << this->getSourceName(objHighDividend);
    _formula << ' '        << this->getSourceName(objLowDividend) << ')';       
   
    // Source2 : diviseur à sign-extend à la taille du dividende
    _formula << " ((_ sign_extend " << lengthOfQuotient << ") " << this->getSourceName(objDivisor) << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AND(const TaintPtr &tPtr)
{
    ObjectSource src0   = tPtr->getSource(0);
    ObjectSource src1   = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvand " << this->getSourceName(src0) << ' ' << this->getSourceName(src1);
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_OR(const TaintPtr &tPtr)
{
    ObjectSource src0   = tPtr->getSource(0);
    ObjectSource src1   = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvor " << this->getSourceName(src0) << ' ' << this->getSourceName(src1);
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_XOR(const TaintPtr &tPtr)
{
    ObjectSource src0   = tPtr->getSource(0);
    ObjectSource src1   = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;
    _formula << "bvxor " << this->getSourceName(src0) << ' ' << this->getSourceName(src1);
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_NOT(const TaintPtr &tPtr)
{
    BEGIN_RELATION_DECLARATION;
    _formula << "bvnot " << this->getSourceName(tPtr->getSource(0));
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SHL(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    _formula << "bvshl " << this->getSourceName(shiftedSrc) << ' ';
    
    // cas ou le décalage est marqué : il faut le masquer avant le shift
    if (displSrc.isSrcTainted())
    {
        // alignement à la longueur de l'opérande déplacée (sauf cas 8 bits : inutile)
        if (lengthOfResult != 8) 
        {  
            _formula << "((_ zero_extend " << lengthOfResult - 8 << ") ";
            _formula << "(bvand " << this->getSourceName(displSrc);
            // masquage à 0x1f (ou 0x3f si 64 bits)
            if (lengthOfResult != 64) _formula << " #x1f))";
            else                      _formula << " #x3f))";
        }
        else // déplacement 8 bits marqué
        {
            _formula << "(bvand " << this->getSourceName(displSrc) << " #x1f)";
        }
    }
    // déplacement non marqué : la valeur a déjà été masquée dans la fonction d'analyse
    else
    {
        // insertion de la valeur numérique du déplacement adapté à la longueur de l'opérande déplacée
        _formula << "(_ bv" << displSrc.getValue() << ' ' << lengthOfResult << ')';
    } 
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SHR(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    _formula << "bvlshr " << this->getSourceName(shiftedSrc) << ' ';
    
    // cas ou le décalage est marqué : il faut le masquer avant le shift
    if (displSrc.isSrcTainted())
    {
        // alignement à la longueur de l'opérande déplacée (sauf cas 8 bits : inutile)
        if (lengthOfResult != 8) 
        {  
            _formula << "((_ zero_extend " << lengthOfResult - 8 << ") ";
            _formula << "(bvand " << this->getSourceName(displSrc);
            // masquage à 0x1f (ou 0x3f si 64 bits)
            if (lengthOfResult != 64) _formula << " #x1f))";
            else                      _formula << " #x3f))";
        }
        else // déplacement 8 bits marqué
        {
            _formula << "(bvand " << this->getSourceName(displSrc) << " #x1f)";
        }
    }
    // déplacement non marqué : la valeur a déjà été masquée dans la fonction d'analyse
    else
    {
        // insertion de la valeur numérique du déplacement adapté à la longueur de l'opérande déplacée
        _formula << "(_ bv" << displSrc.getValue() << ' ' << lengthOfResult << ')';
    } 
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SAR(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    _formula << "bvashr " << this->getSourceName(shiftedSrc) << ' ';
    
    // cas ou le décalage est marqué : il faut le masquer avant le shift
    if (displSrc.isSrcTainted())
    {
        // alignement à la longueur de l'opérande déplacée (sauf cas 8 bits : inutile)
        if (lengthOfResult != 8) 
        {  
            _formula << "((_ zero_extend " << lengthOfResult - 8 << ") ";
            _formula << "(bvand " << this->getSourceName(displSrc);
            // masquage à 0x1f (ou 0x3f si 64 bits)
            if (lengthOfResult != 64) _formula << " #x1f))";
            else                      _formula << " #x3f))";
        }
        else // déplacement 8 bits marqué
        {
            _formula << "(bvand " << this->getSourceName(displSrc) << " #x1f)";
        }
    }
    // déplacement non marqué : la valeur a déjà été masquée dans la fonction d'analyse
    else
    {
        // insertion de la valeur numérique du déplacement adapté à la longueur de l'opérande déplacée
        _formula << "(_ bv" << displSrc.getValue() << ' ' << lengthOfResult << ')';
    } 
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_ROR(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
    // puis calcul modulo size. Cela revient à calculer modulo size tout de suite !!!
    _formula << "let ((maskedDepl (";
    switch (lengthOfResult)
    {
    case 8: 
        // prise du modulo 8, donc AND #x07
        _formula << "bvand " << this->getSourceName(displSrc) << " #x07))) "; 
        break;
    case 16:
        // prise du modulo 16, donc AND #x0f, et zero_extend de 8
        _formula << "( _zero_extend 8) (bvand " << this->getSourceName(displSrc) << " #x0f)))) ";
        break;
    case 32:
        // prise du modulo 32, donc AND #x1f, et zero_extend de 24
        _formula << "( _zero_extend 24) (bvand " << this->getSourceName(displSrc) << " #x1f)))) ";
        break;
    case 64:
        // prise du modulo 64, donc AND #x3f, et zero_extend de 58
        _formula << "( _zero_extend 58) (bvand " << this->getSourceName(displSrc) << " #x3f)))) ";
        break;
    }

    // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_right'
    if (!displSrc.isSrcTainted())
    {
        _formula <<  "(_ rotate_right " << displSrc.getValue() << ") " << this->getSourceName(shiftedSrc);
    }
    else
    {
        // si depl marqué, obligation de passer par deux shifts
        // _rotr(val, depl) = (val >> depl) | (val << (sizeof(val) * 8 - depl))
        // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
        // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend si necessaire

        // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
        _formula << "let ((maskedDepl (";
        // adaptation à la longueur de l'opérande déplacéd (8 bits : inutile)
        if (lengthOfResult == 8) 
        {
            _formula << "bvand " << this->getSourceName(displSrc) << " #x1f))) ";
        }
        else
        {
            _formula << "( _zero_extend " << lengthOfResult - 8 << ") ";
            _formula << "(bvand " << this->getSourceName(displSrc);
            if (lengthOfResult == 64) _formula << " #x3f)))) ";
            else                      _formula << " #x1f)))) ";
        }

        // 1ere partie : (val >> depl) |
        _formula << "(let ((leftPart (bvlshr " << this->getSourceName(shiftedSrc) << " maskedDepl))) ";

        // 2eme partie : (val << (lengthOfResult - depl)) <=> bvshl(rotSrc((_ ze bvsub (lengthInBitsOfResult deplSrc)) 
        _formula << "(let ((rightPart (bvshl " << this->getSourceName(shiftedSrc);
        _formula << " (bvsub (_ bv" << lengthOfResult << ' ' << lengthOfResult << ") maskedDepl)))) ";

        // OU logique des deux parties
        _formula << "(bvor leftPart rightPart)))";
    }

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_ROL(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;
    
    // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_right'
    // le déplacement a déjà été masqué / pris modulo size dans la fonction d'analyse
    if (!displSrc.isSrcTainted())
    {
        _formula <<  "(_ rotate_left " << displSrc.getValue() << ") " << this->getSourceName(shiftedSrc);
    }
    else
    {
        // si depl marqué, obligation de passer par deux shifts
        // _rotl(val, s) = (val << s) | (val >> (sizeof(val) * 8 - s))
        // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
        // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend si nécessaire
        
        // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
        // puis calcul modulo size. Cela revient à calculer modulo size tout de suite !!!
        _formula << "let ((maskedDepl (";
        switch (lengthOfResult)
        {
        case 8: 
            // prise du modulo 8, donc AND #x07
            _formula << "bvand " << this->getSourceName(displSrc) << " #x07))) "; 
            break;
        case 16:
            // prise du modulo 16, donc AND #x0f, et zero_extend de 8
            _formula << "( _zero_extend 8) (bvand " << this->getSourceName(displSrc) << " #x0f)))) ";
            break;
        case 32:
            // prise du modulo 32, donc AND #x1f, et zero_extend de 24
            _formula << "( _zero_extend 24) (bvand " << this->getSourceName(displSrc) << " #x1f)))) ";
            break;
        case 64:
            // prise du modulo 64, donc AND #x3f, et zero_extend de 58
            _formula << "( _zero_extend 58) (bvand " << this->getSourceName(displSrc) << " #x3f)))) ";
            break;
        }

        // 1ere partie : (val << depl) |
        _formula << "(let ((leftPart (bvshl " << this->getSourceName(shiftedSrc) << " maskedDepl))) ";

        // 2eme partie : (val >> (lengthOfResult - depl))
        _formula << "(let ((rightPart (bvlshr " << this->getSourceName(shiftedSrc);
        _formula << " (bvsub (_ bv" << lengthOfResult << ' ' << lengthOfResult << ") maskedDepl)))) ";

        // OU logique des deux parties
        _formula << "(bvor leftPart rightPart)))";
    }
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_RCR(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) , valeur du CF (marqué ou non) 
    // et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc   = tPtr->getSource(0);
    ObjectSource carryFlagSrc = tPtr->getSource(1);
    ObjectSource displSrc     = tPtr->getSource(2);
    UINT32 lengthOfResult     = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;
    
    // variable temporaire = concaténation de l'opérande et du Carry Flag
    // meme si aucun n'est marqué
    _formula << "let ((concatSrc (concat " << this->getSourceName(shiftedSrc);
    _formula << ' ' << this->getSourceName(carryFlagSrc) << "))) (";

    // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_right'
    if (!displSrc.isSrcTainted())
    {
        _formula <<  "(_ rotate_right " << displSrc.getValue() << ") concatSrc)" ;
    }
    else
    {
        // si depl marqué, obligation de passer par deux shifts, comme ROR
        // _rotr(val, depl) = (val >> depl) | (val << (sizeof(val) * 8 - depl))
        // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
        // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend si necessaire

        // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
        // puis calcul modulo size. Cela revient à calculer modulo size tout de suite !!!
        _formula << "let ((maskedDepl (";
        switch (lengthOfResult)
        {
        case 8: 
            // prise du modulo 8, donc AND #x07
            _formula << "bvand " << this->getSourceName(displSrc) << " #x07))) "; 
            break;
        case 16:
            // prise du modulo 16, donc AND #x0f, et zero_extend de 8
            _formula << "( _zero_extend 8) (bvand " << this->getSourceName(displSrc) << " #x0f)))) ";
            break;
        case 32:
            // prise du modulo 32, donc AND #x1f, et zero_extend de 24
            _formula << "( _zero_extend 24) (bvand " << this->getSourceName(displSrc) << " #x1f)))) ";
            break;
        case 64:
            // prise du modulo 64, donc AND #x3f, et zero_extend de 58
            _formula << "( _zero_extend 58) (bvand " << this->getSourceName(displSrc) << " #x3f)))) ";
            break;
        }

        // 1ere partie : (val >> depl) |
        _formula << "(let ((leftPart (bvlshr concatSrc maskedDepl))) ";

        // 2eme partie : (val << (lengthOfResult - depl))
        _formula << "(let ((rightPart (bvshl concatSrc (bvsub (_ bv" << lengthOfResult << ' ' << lengthOfResult << ") maskedDepl)))) ";

        // OU logique des deux parties
        _formula << "(bvor leftPart rightPart))))";
    }

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_RCL(const TaintPtr &tPtr)
{
    // récupération des sources : opérande déplacée (marqué ou non) , valeur du CF (marqué ou non) 
    // et valeur du déplacement (marqué ou non)
    ObjectSource shiftedSrc   = tPtr->getSource(0);
    ObjectSource carryFlagSrc = tPtr->getSource(1);
    ObjectSource displSrc     = tPtr->getSource(2);
    UINT32 lengthOfResult     = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;
    
    // variable temporaire = concaténation de l'opérande et du Carry Flag
    // meme si aucun n'est marqué
    _formula << "let ((concatSrc (concat " << this->getSourceName(shiftedSrc);
    _formula << ' ' << this->getSourceName(carryFlagSrc) << "))) (";

    // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_left'
    if (!displSrc.isSrcTainted())
    {
        _formula <<  "(_ rotate_left " << displSrc.getValue() << ") concatSrc)" ;
    }
    else
    {
        // si depl marqué, obligation de passer par deux shifts, comme ROL
        // _rotl(val, depl) = (val << depl) | (val >> (sizeof(val) * 8 - depl))
        // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
        // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend si necessaire

        // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
        // puis calcul modulo size. Cela revient à calculer modulo size tout de suite !!!
        _formula << "let ((maskedDepl (";
        switch (lengthOfResult)
        {
        case 8: 
            // prise du modulo 8, donc AND #x07
            _formula << "bvand " << this->getSourceName(displSrc) << " #x07))) "; 
            break;
        case 16:
            // prise du modulo 16, donc AND #x0f, et zero_extend de 8
            _formula << "( _zero_extend 8) (bvand " << this->getSourceName(displSrc) << " #x0f)))) ";
            break;
        case 32:
            // prise du modulo 32, donc AND #x1f, et zero_extend de 24
            _formula << "( _zero_extend 24) (bvand " << this->getSourceName(displSrc) << " #x1f)))) ";
            break;
        case 64:
            // prise du modulo 64, donc AND #x3f, et zero_extend de 58
            _formula << "( _zero_extend 58) (bvand " << this->getSourceName(displSrc) << " #x3f)))) ";
            break;
        }

        // 1ere partie : (val << depl) |
        _formula << "(let ((leftPart (bvshl shlconcatSrc maskedDepl))) ";

        // 2eme partie : (val >> (lengthOfResult - depl)) 
        _formula << "(let ((rightPart (bvlshr concatSrc (bvsub (_ bv" << lengthOfResult << ' ' << lengthOfResult << ") maskedDepl)))) ";

        // OU logique des deux parties
        _formula << "(bvor leftPart rightPart))))";
    }

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SETCC(const TaintPtr &tPtr) 
{
    // déclaration similiaire à un predicat sauf qu'on déclare un objet sur 8 bits (et non un booléen)
    // et que les objets représentant les flags sont fournis (et non pas à récupérer via TaintManager)
    // formule générique : "ite (PREDICAT VRAI) #x01 #x00"
    PREDICATE pred = static_cast<PREDICATE>(tPtr->getSource(0).getValue());
    
    BEGIN_RELATION_DECLARATION;
    
    _formula << "ite (";

    switch (pred)
    {  
    // test d'un seul flag, mis à 1, présent en source1
    case PREDICATE_BELOW: 	// Below (CF==1).
    case PREDICATE_SIGN:    // Sign (SF==1).
    case PREDICATE_ZERO: 	// Zero (ZF==1).
    case PREDICATE_OVERFLOW:// Overflow (OF==1).
    case PREDICATE_PARITY: 	// Parity (PF==1)
        _formula << "= " << this->getSourceName(tPtr->getSource(1)) << " #b1";
        break;

    // test d'un seul flag, mis à 0, présent en source1
    case PREDICATE_NOT_BELOW: 	// Not Below (CF==0)
    case PREDICATE_NOT_SIGN:	// Not Sign (SF==0)
    case PREDICATE_NOT_ZERO:	// Not Zero (ZF==0)
    case PREDICATE_NOT_OVERFLOW:// Not Overflow (OF==0)
    case PREDICATE_NOT_PARITY: 	// Not Parity (PF==0)
        _formula << "= " << this->getSourceName(tPtr->getSource(1)) << " #b0";
        break;
    
    // deux flags, SF et OF, en sources 1 et 2
    case PREDICATE_LESS: 	    // Less (SF!=OF), (ou SF XOR OF = 1)
        _formula << "= (bvxor " << this->getSourceName(tPtr->getSource(1));
        _formula << ' ' << this->getSourceName(tPtr->getSource(2)) << ") #b1";
        break;

    // deux flags, SF et OF, en sources 1 et 2
    case PREDICATE_NOT_LESS: 	// Greater or Equal (SF==OF). (ou SF XOR OF = 0)
        _formula << "= (bvxor " << this->getSourceName(tPtr->getSource(1));
        _formula << ' ' << this->getSourceName(tPtr->getSource(2)) << ") #b0";
        break;

    // deux flags, CF et ZF, en sources 1 et 2
    case PREDICATE_BELOW_OR_EQUAL: 	    // Below or Equal (CF==1 or ZF==1), ou (CF or ZF) == 1
        _formula << "= (bvor " << this->getSourceName(tPtr->getSource(1));
        _formula << ' ' << this->getSourceName(tPtr->getSource(2)) << ") #b1";
        break;
    
    // deux flags, CF et ZF, en sources 1 et 2
    case PREDICATE_NOT_BELOW_OR_EQUAL: 	// Above (CF==0 and ZF==0), ou (CF or ZF) == 0
        _formula << "= (bvor " << this->getSourceName(tPtr->getSource(1));
        _formula << ' ' << this->getSourceName(tPtr->getSource(2)) << ") #b0";
        break;

    // trois flags, SF, OF et ZF, en sources 1, 2 et 3   
    case PREDICATE_LESS_OR_EQUAL: // Less or Equal (ZF==1 or SF!=OF), ou ((SF ^ OF) or ZF) == 1
        _formula << "= (bvor " << this->getSourceName(tPtr->getSource(3)); // source3 = ZF
        _formula << " (bvxor " << this->getSourceName(tPtr->getSource(1)); // source1 = SF
        _formula << ' ' << this->getSourceName(tPtr->getSource(2)) << ")) #b1"; // source2 = OF
        break;

    // trois flags, SF, OF et ZF, en sources 1, 2 et 3 
    case PREDICATE_NOT_LESS_OR_EQUAL: // Greater (ZF==0 and SF==OF),  ou ((SF ^ OF) or ZF) == 0
        _formula << "= (bvor " << this->getSourceName(tPtr->getSource(3)); // source3 = ZF
        _formula << " (bvxor " << this->getSourceName(tPtr->getSource(1)); // source1 = SF
        _formula << ' ' << this->getSourceName(tPtr->getSource(2)) << ")) #b1"; // source2 = OF
        break;
    }

    // 1 si prédicat Vrai, 0 sinon (le tout sur 8bits)
    _formula << ") #x01 #x00";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_COMPLEMENT_BIT(const TaintPtr &tPtr)
{
    // COMPLEMENT_BIT : XOR de la source avec (1<<numero bit). Correspond à BTC
    // numéro du bit est pris modulo 16/32/64 (soit un AND avec 15/31/63)
    // ici la position du bit est marquée, sinon l'operation aurait été faite par un XOR direct 
    // dans la fonction d'analyse
    
    ObjectSource operandSrc        = tPtr->getSource(0);
    const std::string bitNumberSrc = tPtr->getSource(1).getTaintedSource()->getName();
    UINT32 lengthOfResult          = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire : numéro bit MODULO 16/32/64
    _formula << "let ((maskedNumber (bvand (_ bv" << lengthOfResult - 1 << " " << lengthOfResult << ") " ;
    _formula << bitNumberSrc << "))) ";

    // variable temporaire : (1 << numerobit)
    _formula << "(let ((bitNumber (bvshl (_ bv1 " << lengthOfResult << ") maskedNumber))) ";
   
    // inversion du bit via XOR
    _formula << "(bvxor bitNumber " << this->getSourceName(operandSrc) << "))";

     END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SET_BIT(const TaintPtr &tPtr)
{
    // SET_BIT : OR de la source avec (1<<numero bit). Correspond à BTS
    // numéro du bit est pris modulo 16/32/64 (soit un AND avec 15/31/63)
    // ici la position du bit est marquée, sinon l'operation aurait été faite par un OR direct 
    // dans la fonction d'analyse
    
    ObjectSource operandSrc        = tPtr->getSource(0);
    const std::string bitNumberSrc = tPtr->getSource(1).getTaintedSource()->getName();
    UINT32 lengthOfResult          = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire : numéro bit MODULO 16/32/64
    _formula << "let ((maskedNumber (bvand (_ bv" << lengthOfResult - 1 << " " << lengthOfResult << ") " ;
    _formula << bitNumberSrc << "))) ";

    // variable temporaire : (1 << numerobit)
    _formula << "(let ((bitNumber (bvshl (_ bv1 " << lengthOfResult << ") maskedNumber))) ";
   
    // mise à 1 du bit via OR
    _formula << "(bvor bitNumber " << this->getSourceName(operandSrc) << "))";

     END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_CLEAR_BIT(const TaintPtr &tPtr)
{
    // CLEAR_BIT : AND de la source avec ~(1<<numero bit). Correspond à BTR
    // numéro du bit est pris modulo 16/32/64 (soit un AND avec 15/31/63)
    // ici la position du bit est marquée, sinon l'operation aurait été faite par un AND direct 
    // dans la fonction d'analyse

    ObjectSource operandSrc        = tPtr->getSource(0);
    const std::string bitNumberSrc = tPtr->getSource(1).getTaintedSource()->getName();
    UINT32 lengthOfResult          = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire : numéro bit MODULO 16/32/64
    _formula << "let ((maskedNumber (bvand (_ bv" << lengthOfResult - 1 << " " << lengthOfResult << ") " ;
    _formula << bitNumberSrc << "))) ";

    // variable temporaire : NOT(1 << numerobit)
    _formula << "(let ((notBitNumber (bvnot (bvshl (_ bv1 " << lengthOfResult << ") maskedNumber)))) ";
   
    // mise à zero du bit via AND
    _formula << "(bvand notBitNumber " << this->getSourceName(operandSrc) << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_BSF(const TaintPtr &tPtr)
{
    /* Bit Scan Forward : index du LSB de la source
    cet index vaut index64[((bb ^ (bb-1)) * debruijn64) >> 58]
    les variables intermédiaires seront implémentées via des 'let'
    Le calcul se fait sur 64 bits : la source devra être zero extended
    à 64bits si elle ne l'est pas. Exemple pour une source de 32 bits:
    (define-fun BSF32 () (_ BitVec 32) (
        let ((bb TDW1)) 
        (let ((bbMin1 (bvsub bb (_ bv1 32)))) 
        (let ((bbXor (bvxor bb bbMin1)))
        (let ((bbZeroExt ((_ zero_extend 32) bbXor))) 
        (let ((bbMul (bvmul bbZeroExt constante))) 
        (let ((bbShift (bvlshr bbMul (_ bv58 64)))) 
        ((_ extract 31 0) (index64 bbShift)))))))))  => ce qui sera affecté à BSF */

    ObjectSource operandSrc = tPtr->getSource(0);
    UINT32 lengthOfSource   = operandSrc.getLength();

    // si le tableau et la constante n'ont pas encore été déclaré, le faire
    if (!_isDeBruijnDeclared) _formula << this->getDeBruijnArray();

    BEGIN_RELATION_DECLARATION;

    // bb = operande source
    _formula << "\n  let ((bb " << this->getSourceName(operandSrc) <<"))\n";
    // bbMin1 = bb-1
    _formula << "  (let ((bbMin1 (bvsub bb (_ bv1 " << lengthOfSource << "))))\n";
    // bbXor = bb ^ (bb-1)
    _formula << "  (let ((bbXor (bvxor bb bbMin1)))\n";
        
    // si la source n'est pas sur 64 bits, l'adapter à cette taille
    if (lengthOfSource != 64)
    {
        _formula << "  (let ((bbZeroExt ((_ zero_extend " << 64 - lengthOfSource << ") bbXor)))\n";
        // multiplication par la constante
        _formula << "  (let ((bbMul (bvmul bbZeroExt constante)))\n";
        // shift de 58 bits
        _formula << "  (let ((bbShift (bvlshr bbMul (_ bv58 64))))\n";
        // extraction sur 'length' bits de la valeur du tableau à l'index calculé
        _formula << "  ((_ extract " << lengthOfSource - 1 << " 0) (index64 bbShift))";
        // 5 lets (en dehors du premier) => 5 parenthèses fermantes
        _formula << ")))))";
    }
    else 
    {
        _formula << "  (let ((bbMul (bvmul bbXor constante)))\n";
        // shift de 58 bits
        _formula << "  (let ((bbShift (bvlshr bbMul (_ bv58 64))))\n";
        // récupération de la valeur du tableau à l'index calculé
        _formula << "  (index64 bbShift)";
        // 4 lets (en dehors du premier) => 4 parenthèses fermantes
        _formula << "))))";
    }        

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_BSR(const TaintPtr &tPtr)
{
    /* Bit Scan Reverse : index du MSB de la source
    cet index vaut :
    bb |= bb >> 1; bb |= bb >> 2;  bb |= bb >> 4; bb |= bb >> 8; 
     ajout de bb |= bb >> 16; (cas 32 et 64bits)
     ajout de bb |= bb >> 32; (cas 64bits)
    index = index64[(bb * debruijn64) >> 58];
        
    les variables intermédiaires seront implémentées via des 'let'
    Le calcul se fait sur 64 bits : la source devra être zero extended si besoin. 
    TODO : en 32bits on s'arrete au shift16. En 16 bits on s'arrete au shift8
       
    Exemple pour une source de 32 bits:
        (define-fun BSR32 () (_ BitVec 32) (
        let ((bbShift0 TDW1)) 
        (let ((bbShift1 (bvor bbShift0 (bvlshr bbShift0 (_ bv1 32))))) 
        (let ((bbShift2 (bvor bbShift1 (bvlshr bbShift1 (_ bv2 32))))) 
        (let ((bbShift3 (bvor bbShift2 (bvlshr bbShift2 (_ bv4 32))))) 
        (let ((bbShift4 (bvor bbShift3 (bvlshr bbShift3 (_ bv8 32))))) 
        (let ((bbShift5 (bvor bbShift4 (bvlshr bbShift4 (_ bv16 32))))) 
            (let ((bbShift6 (bvor bbShift5 (bvlshr bbShift5 (_ bv32 32))))) => NON FAIT CAR 32BITS
        (let ((bbPosition ((_ zero_extend 32) bbShift5))) => ZERO_EXTEND car calcul sur 64bits
        (let ((bbMul (bvmul bbPosition constante))) 
        (let ((bbShift (bvlshr bbMul (_ bv58 64)))) 
        ((_ extract 31 0) (index64 bbShift)))))))))))) => ce qui sera affecté à BSR32 */

    ObjectSource operandSrc = tPtr->getSource(0);
    UINT32 lengthOfSource   = operandSrc.getLength();

    // si le tableau et la constante n'ont pas encore été déclaré, le faire
    if (!_isDeBruijnDeclared) _formula << this->getDeBruijnArray();

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((bbShift0 " << this->getSourceName(operandSrc) << " ))\n";

    // bb |= bb >> 1;
    _formula << "(let ((bbShift1 (bvor bbShift0 (bvlshr bbShift0 (_ bv1 " << lengthOfSource << ")))))\n";
    // bb |= bb >> 2;
    _formula << "(let ((bbShift2 (bvor bbShift1 (bvlshr bbShift1 (_ bv2 " << lengthOfSource << ")))))\n";
    // bb |= bb >> 4;
    _formula << "(let ((bbShift3 (bvor bbShift2 (bvlshr bbShift2 (_ bv4 " << lengthOfSource << ")))))\n";
    // bb |= bb >> 8; C'est le dernier shift dans le cas 16 bits
    _formula << "(let ((bbShift4 (bvor bbShift3 (bvlshr bbShift3 (_ bv8 " << lengthOfSource << ")))))\n";

    if (lengthOfSource == 16)  _formula << "(let ((bbPosition ((_ zero_extend 48) bbShift4)))\n";
    else // cas 32 et 64 bits
    {
        // bb |= bb >> 16; C'est le dernier shift dans le cas 32 bits
        _formula << "(let ((bbShift5 (bvor bbShift4 (bvlshr bbShift4 (_ bv16 " << lengthOfSource << ")))))\n";
        if (lengthOfSource == 32)  _formula << "(let ((bbPosition ((_ zero_extend 32) bbShift5)))\n";
        else // cas 64 bits
        {
            // bb |= bb >> 32; C'est le dernier shift dans le cas 64 bits, et pas besoin de l'étendre
            _formula << "(let ((bbPosition (bvor bbShift5 (bvlshr bbShift5 (_ bv32 " << lengthOfSource << ")))))\n";
        }
    }

    // multiplication par la constante, et shift
    _formula << "  (let ((bbMul (bvmul bbPosition constante)))\n" \
                "  (let ((bbShift (bvlshr bbMul (_ bv58 64))))\n";

    // récupération de la valeur dans le tableau. Mise à la taille du resultat par une extraction si besoin
    if (lengthOfSource != 64)
    {
        _formula << "  ((_ extract " << lengthOfSource - 1 << " 0) (index64 bbShift))";
        // nombre de parenthèses fermantes = 7 dans le cas 16 bits, une de plus dans le cas 32bits
        _formula << ")))))))";
        if (lengthOfSource == 32) _formula << ')';
    }
    else _formula << "  (index64 bbShift)))))))))";// 8 parenthèses fermantes pour les variables temporaires

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAA_AL(const TaintPtr &tPtr)
{
    // condition de AAA : "IF (((AL and 0FH) > 9) or (AF=1)"
    // condition vraie  => AL = (AL + 6) & 0xF
    // condition fausse => AL = AL & 0xF
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src0) #x09) (= src1 #b1)))) 
    //  (ite (= condition true) (bvand #x0f (bvadd src0 #x06)) (bvand #x0f src0))

    ObjectSource objAL         = tPtr->getSource(0);
    ObjectSource objAuxFlag    = tPtr->getSource(1);
    const std::string stringAL = this->getSourceName(objAL);

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << stringAL << ") #x09) ";
    _formula <<                     "(= " << this->getSourceName(objAuxFlag) << " #b1)))) \n";
    _formula << "(ite (= condition true) (bvand #x0f (bvadd " << stringAL << " #x06))";
    _formula <<                        " (bvand #x0f "<< stringAL << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAA_AH(const TaintPtr &tPtr)
{
    // condition de AAA : "IF (((AL and 0FH) > 9) or (AF=1)"
    // condition vraie  => AH = AH + 1
    // condition fausse => AH INCHANGE
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src0) #x09) (= src1 #b1)))) 
    //  (ite (= condition true) (bvadd src0 #x01) src0)

    ObjectSource objAL         = tPtr->getSource(0);
    ObjectSource objAuxFlag    = tPtr->getSource(1);
    const std::string stringAL = this->getSourceName(objAL);

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << stringAL << ") #x09) ";
    _formula <<                     "(= " << this->getSourceName(objAuxFlag) << " #b1)))) \n";
    _formula << "(ite (= condition true) (bvadd " << stringAL << " #x01) " << stringAL << ")";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAD(const TaintPtr &tPtr)
{
    // AL = (AL + (AH ∗ imm8)) & xFF (le AND FF ne sert à rien ici car AL est sur 8 bits...)
    // formule SMT-LIB : 
    // bvadd src0 (bvmul src1 src2)

    const std::string stringAL   = this->getSourceName(tPtr->getSource(0));
    const std::string stringAH   = this->getSourceName(tPtr->getSource(1));
    const std::string stringBase = this->getSourceName(tPtr->getSource(2));

    BEGIN_RELATION_DECLARATION;
    _formula << "bvadd " << stringAL << " (bvmul " << stringAH << ' ' << stringBase << ')';
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAM_AL(const TaintPtr &tPtr)
{
    // AL = AL(src0) MOD BASE(src1)

    BEGIN_RELATION_DECLARATION;
    _formula << "bvurem " << this->getSourceName(tPtr->getSource(0)); // src0 = AL
    _formula <<       ' ' << this->getSourceName(tPtr->getSource(1)); // src1 = base
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAM_AH(const TaintPtr &tPtr)
{
    // AH = AL(src0) DIV BASE(src1)

    BEGIN_RELATION_DECLARATION;
    _formula << "bvudiv " << this->getSourceName(tPtr->getSource(0)); // src0 = AL
    _formula <<       ' ' << this->getSourceName(tPtr->getSource(1)); // src1 = base
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAS_AL(const TaintPtr &tPtr)
{
    // condition de AAS : "IF (((AL and 0FH) > 9) or (AF=1)" (idem AAA)
    // condition vraie  => AL = ([0..7](AX - 6)) & 0xF
    // condition fausse => AL = AL & 0xF
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src1) #x09) (= src2 #b1))))
    //  (let ((AX (concat src0 src1)))
    //   (ite (= condition true) (bvand #x0f ((_ extract 7 0) (bvsub AX #x0006))) src1))

    const std::string stringAH      = this->getSourceName(tPtr->getSource(0));
    const std::string stringAL      = this->getSourceName(tPtr->getSource(1));
    const std::string stringAuxFlag = this->getSourceName(tPtr->getSource(2));

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << stringAL << ") #x09) (= " << stringAuxFlag << " #b1))))\n";
    _formula << "  (let ((AX (concat " << stringAH << ' ' << stringAL << ")))\n";
    _formula << "   (ite (= condition true) (bvand #x0f ((_ extract 7 0) (bvsub AX #x0006))) " << stringAL << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_AAS_AH(const TaintPtr &tPtr)
{
    // condition de AAS : "IF (((AL and 0FH) > 9) or (AF=1)" (idem AAA)
    // condition vraie  => AH = ([15..8](AX - 6)) - 1, equivalent à [15..8](AX - 0x0106)
    // condition fausse => AH inchangé
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src1) #x09) (= src2 #b1))))
    //  (let ((AX (concat src0 src1)))
    //   (ite (= condition true) ((_ extract 15 8) (bvsub AX #x0106)) src0))

    const std::string stringAH      = this->getSourceName(tPtr->getSource(0));
    const std::string stringAL      = this->getSourceName(tPtr->getSource(1));
    const std::string stringAuxFlag = this->getSourceName(tPtr->getSource(2));

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << stringAL << ") #x09) (= " << stringAuxFlag << " #b1))))\n";
    _formula << "  (let ((AX (concat " << stringAH << ' ' << stringAL << ")))\n";
    _formula << "   (ite (= condition true) ((_ extract 15 8) (bvsub AX #x0106)) " << stringAH << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DAA_1ST(const TaintPtr &tPtr)
{
    // 1ere condition de DAA : "IF (((AL and 0FH) > 9) or (AF=1)" (idem AAA)
    // condition vraie  => AL = AL + 6 (sans masquage à 0xF)
    // condition fausse => AL inchangé
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src0) #x09) (= src1 #b1))))
    //   (ite (= condition true) (bvadd src0 #x06) src0)

    const std::string stringAL      = this->getSourceName(tPtr->getSource(0));
    const std::string stringAuxFlag = this->getSourceName(tPtr->getSource(1));

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << stringAL << ") #x09) (= " << stringAuxFlag << " #b1))))\n";
    _formula << "   (ite (= condition true) (bvadd " << stringAL << " #x06) " << stringAL << ')';

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DAA_2ND(const TaintPtr &tPtr)
{
    // 2eme condition de DAA : "IF (((OLD_AL > 0x99) or (OldCF=1)" 
    // condition vraie  => ALApres1ereCondition = ALApres1ereCondition + 0x60
    // condition fausse => ALApres1ereCondition inchangé
    // formule SMT-LIB : 
    // let ((condition (or (bvugt src0 #x99) (= src1 #b1))))
    //   (ite (= condition true) (bvadd src2 #x60) src2)

    const std::string stringAL             = this->getSourceName(tPtr->getSource(0));
    const std::string stringCarryFlag      = this->getSourceName(tPtr->getSource(1));
    const std::string stringALAfterDAA_1ST = this->getSourceName(tPtr->getSource(2));

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt " << stringAL << " #x99) (= " << stringCarryFlag << " #b1))))\n";
    _formula << " (ite (= condition true) (bvadd " << stringALAfterDAA_1ST << " #x60) " << stringALAfterDAA_1ST << ')';

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DAS_1ST(const TaintPtr &tPtr)
{
    // 1ere condition de DAS : "IF (((AL and 0FH) > 9) or (AF=1)" (idem AAA)
    // condition vraie  => AL = AL - 6 (sans masquage à 0xF)
    // condition fausse => AL inchangé
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src0) #x09) (= src1 #b1))))
    //   (ite (= condition true) (bvsub src0 #x06) src0)

    const std::string stringAL      = this->getSourceName(tPtr->getSource(0));
    const std::string stringAuxFlag = this->getSourceName(tPtr->getSource(1));

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << stringAL << ") #x09) (= " << stringAuxFlag << " #b1))))\n";
    _formula << "   (ite (= condition true) (bvsub " << stringAL << " #x06) " << stringAL << ')';

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_DAS_2ND(const TaintPtr &tPtr)
{
    // 2eme condition de DAS : "IF (((OLD_AL > 0x99) or (OldCF=1)" 
    // condition vraie  => ALApres1ereCondition = ALApres1ereCondition - 0x60
    // condition fausse => ALApres1ereCondition inchangé
    // formule SMT-LIB : 
    // let ((condition (or (bvugt src0 #x99) (= src1 #b1))))
    //   (ite (= condition true) (bvsub src2 #x60) src2)

    const std::string stringAL             = this->getSourceName(tPtr->getSource(0));
    const std::string stringCarryFlag      = this->getSourceName(tPtr->getSource(1));
    const std::string stringALAfterDAA_1ST = this->getSourceName(tPtr->getSource(2));

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt " << stringAL << " #x99) (= " << stringCarryFlag << " #b1))))\n";
    _formula << " (ite (= condition true) (bvsub " << stringALAfterDAA_1ST << " #x60) " << stringALAfterDAA_1ST << ')';

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_X_SALC(const TaintPtr &tPtr)
{
    // si CF == 0 => AL = 0 ; si CF == 1 => AL = FF
    // formule SMT-LIB : ite (= src0 #b0) #x00 #xff (source0 sur 1 bit et forcément marquée)

    BEGIN_RELATION_DECLARATION;
    _formula << "ite (= #b0 " << tPtr->getSource(0).getTaintedSource()->getName() << ") #x00 #xff";
    END_RELATION_DECLARATION;
}

// flags

void TranslateToSMTLIB::translate_F_LSB(const TaintPtr &tPtr)
{
    BEGIN_RELATION_DECLARATION;
    // extraction du bit de poids faible de l'unique source
    _formula << "(_ extract 0 0) " << this->getSourceName(tPtr->getSource(0)); 
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_MSB(const TaintPtr &tPtr)
{
    ObjectSource src0  = tPtr->getSource(0);
    UINT32 msbIndex    = src0.getLength() - 1;

    BEGIN_RELATION_DECLARATION;
    // extraction du bit de poids fort de l'unique source
    _formula << "(_ extract " << msbIndex << ' ' << msbIndex << ") " << this->getSourceName(src0); 
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_ADD(const TaintPtr &tPtr)
{
    // Extension d'1 bit des opérandes afin d'extraire le bit fort de leur somme
    ObjectSource src0  = tPtr->getSource(0);
    ObjectSource src1  = tPtr->getSource(1);
    UINT32 extractBit  = src0.getLength(); // bit de poids fort des opérandes étendues

    BEGIN_RELATION_DECLARATION;

    _formula << "(_ extract " << extractBit << ' ' << extractBit << ") ";
    _formula << "(bvadd ((_ zero_extend 1) " << this->getSourceName(src0) << ") ";
    _formula <<        "((_ zero_extend 1) " << this->getSourceName(src1) << "))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_SUB(const TaintPtr &tPtr)
{
    ObjectSource src0  = tPtr->getSource(0);
    ObjectSource src1  = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;

    // SUB provoque une retenue si op1 < op2. En SMTLIB utilisation de bvult qui renvoie true si op 1 < op 2
    _formula << "ite (bvult " << this->getSourceName(src0) \
                       << ' ' << this->getSourceName(src1) << ") #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_NEG(const TaintPtr &tPtr)
{
    ObjectSource src0  = tPtr->getSource(0);
    UINT32 lengthOfSrc = src0.getLength();

    BEGIN_RELATION_DECLARATION;
    
    // comparaison de la source au nombre 0 représenté sur "lengthInBits" bits
    _formula << "ite (= (_ bv0 " << lengthOfSrc << ") " << this->getSourceName(src0);
    _formula << ") #b0 #b1";
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_MUL(const TaintPtr &tPtr)
{
    // CARRY_MUL : Source0 : resultat. Si partie haute du resultat nulle, CF mis à 0
    ObjectSource src0       = tPtr->getSource(0);
    UINT32 lengthOfSrc      = src0.getLength();
    UINT32 lengthOfHighPart = lengthOfSrc >> 1;
 
    BEGIN_RELATION_DECLARATION;

    _formula << "ite (= (_ bv0 " << lengthOfHighPart << ") ";
    _formula <<        "((_ extract " << lengthOfSrc - 1 << ' ' << lengthOfHighPart - 1 << ") ";
    _formula <<  src0.getTaintedSource()->getName() << ") #b0 #b1";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_IMUL(const TaintPtr &tPtr)
{
    // CARRY_IMUL : Source0 : resultat; si resultat = sign_extend partie basse, alors CF mis à 0
    ObjectSource src0      = tPtr->getSource(0);
    UINT32 lengthOfSrc     = src0.getLength();
    UINT32 lengthOfLowPart = lengthOfSrc >> 1;
    const std::string src0Name(src0.getTaintedSource()->getName());
 
    BEGIN_RELATION_DECLARATION;

    // variable temporaire : partie basse du resultat
    _formula << "let ((lowPart ((_ extract " << lengthOfLowPart - 1 << " 0) " << src0Name << ")))\n";
    _formula << "( ite (= ((_ sign_extend " << lengthOfLowPart << ") lowPart) " << src0Name << ") #b0 #b1)";
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_SHL(const TaintPtr &tPtr)
{
    // dernier bit ejecté vers la gauche = bit (lengthInBits - count) de la source
    // récupération par LSB (src >> (lengthInBits - count))
    // ici count est marqué, sinon la fonction d'analyse aurait traité directement
    // par un EXTRACT. ATTENTION : count doit etre auparavant masqué à 0x1f ou 0x3f

    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);   // déplacement marqué et sur 8 bits
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
    // et adaptation à la longueur de l'opérande déplacée (8 bits : inutile)
    _formula << "let ((maskedDepl (";   
    if (lengthOfResult == 8) 
    {
        _formula << "bvand " << displSrc.getTaintedSource()->getName() << " #x1f))) ";
    }
    else
    {
        _formula << "( _zero_extend " << lengthOfResult - 8 << ") ";
        _formula << "(bvand " << displSrc.getTaintedSource()->getName();
        if (lengthOfResult == 64) _formula << " #x3f)))) ";
        else                      _formula << " #x1f)))) ";
    }

    // variable temporaire = src >> (lengthInBits - count)
    _formula << "(let ((lastBitShifted (bvlshr " << this->getSourceName(shiftedSrc);
    _formula << " (bvsub (_ bv" << lengthOfResult << ' ' << lengthOfResult << ") maskedDepl)))) ";

    // LSB de cette variable
    _formula << "((_ extract 0 0) lastBitShifted))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_SHR(const TaintPtr &tPtr) // SAR = idem
{
    // dernier bit ejecté vers la gauche = bit (count - 1) de la source
    // récupération par LSB (src >> (count - 1))
    // ici count est marqué, sinon la fonction d'analyse aurait traité directement
    // par un EXTRACT. ATTENTION : count doit etre auparavant masqué à 0x1f ou 0x3f

    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);   // déplacement marqué et sur 8 bits
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
    // et adaptation à la longueur de l'opérande déplacée (8 bits : inutile)
    _formula << "let ((maskedDepl (";   
    if (lengthOfResult == 8) 
    {
        _formula << "bvand " << displSrc.getTaintedSource()->getName() << " #x1f))) ";
    }
    else
    {
        _formula << "( _zero_extend " << lengthOfResult - 8 << ") ";
        _formula << "(bvand " << displSrc.getTaintedSource()->getName();
        if (lengthOfResult == 64) _formula << " #x3f)))) ";
        else                      _formula << " #x1f)))) ";
    }

    // variable temporaire = src >> (count - 1)
    _formula << "(let ((lastBitShifted (bvlshr " << this->getSourceName(shiftedSrc);
    _formula << " (bvsub maskedDepl (_ bv1 " << lengthOfResult << "))))) ";

    // LSB de cette variable
    _formula << "((_ extract 0 0) lastBitShifted))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_RCL(const TaintPtr &tPtr)
{
    // dernier bit ejecté vers la gauche = bit (lengthInBits - count) de la source
    // récupération par LSB (src >> (lengthInBits - count))
    // ici count est marqué, sinon la fonction d'analyse aurait traité directement
    // par un EXTRACT

    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);   // déplacement marqué et sur 8 bits
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
    // puis calcul modulo size. Cela revient à calculer modulo size tout de suite !!!
    _formula << "let ((maskedDepl (";
    switch (lengthOfResult)
    {
    case 8: 
        // prise du modulo 8, donc AND #x07
        _formula << "bvand " << this->getSourceName(displSrc) << " #x07))) "; 
        break;
    case 16:
        // prise du modulo 16, donc AND #x0f, et zero_extend de 8
        _formula << "( _zero_extend 8) (bvand " << this->getSourceName(displSrc) << " #x0f)))) ";
        break;
    case 32:
        // prise du modulo 32, donc AND #x1f, et zero_extend de 24
        _formula << "( _zero_extend 24) (bvand " << this->getSourceName(displSrc) << " #x1f)))) ";
        break;
    case 64:
        // prise du modulo 64, donc AND #x3f, et zero_extend de 58
        _formula << "( _zero_extend 58) (bvand " << this->getSourceName(displSrc) << " #x3f)))) ";
        break;
    }

    // variable temporaire = src >> (lengthInBits - count)
    _formula << "(let ((lastBitShifted (bvlshr " << this->getSourceName(shiftedSrc);
    _formula << " (bvsub (_ bv" << lengthOfResult << ' ' << lengthOfResult << ") maskedDepl)))) ";

    // LSB de cette variable
    _formula << "((_ extract 0 0) lastBitShifted))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_RCR(const TaintPtr &tPtr)
{
    // dernier bit ejecté vers la droite = bit (count - 1) de la source
    // récupération par LSB (src >> (count - 1))
    // ici count est marqué, sinon la fonction d'analyse aurait traité directement
    // par un EXTRACT

    ObjectSource shiftedSrc = tPtr->getSource(0);
    ObjectSource displSrc   = tPtr->getSource(1);   // déplacement marqué et sur 8 bits
    UINT32 lengthOfResult   = tPtr->getLength();

    BEGIN_RELATION_DECLARATION;

    // variable temporaire = masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
    // puis calcul modulo size. Cela revient à calculer modulo size tout de suite !!!
    _formula << "let ((maskedDepl (";
    switch (lengthOfResult)
    {
    case 8: 
        // prise du modulo 8, donc AND #x07
        _formula << "bvand " << this->getSourceName(displSrc) << " #x07))) "; 
        break;
    case 16:
        // prise du modulo 16, donc AND #x0f, et zero_extend de 8
        _formula << "( _zero_extend 8) (bvand " << this->getSourceName(displSrc) << " #x0f)))) ";
        break;
    case 32:
        // prise du modulo 32, donc AND #x1f, et zero_extend de 24
        _formula << "( _zero_extend 24) (bvand " << this->getSourceName(displSrc) << " #x1f)))) ";
        break;
    case 64:
        // prise du modulo 64, donc AND #x3f, et zero_extend de 58
        _formula << "( _zero_extend 58) (bvand " << this->getSourceName(displSrc) << " #x3f)))) ";
        break;
    }

    // variable temporaire = src >> (count - 1)
    _formula << "(let ((lastBitShifted (bvlshr " << this->getSourceName(shiftedSrc);
    _formula << " (bvsub maskedDepl (_ bv1" << lengthOfResult <<"))))) ";

    // LSB de cette variable
    _formula << "((_ extract 0 0) lastBitShifted))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_BITBYTE(const TaintPtr &tPtr)
{
    // extraction du bit 'source1' de 'source0'. Effectué par LSB(src0 >> src1)
    ObjectSource testedSrc    = tPtr->getSource(0);
    ObjectSource bitNumberSrc = tPtr->getSource(1);
    UINT32 lengthOfSource     = testedSrc.getLength(); // nombre de bits de la source

    BEGIN_RELATION_DECLARATION;

    _formula << "(_ extract 0 0) (bvlshr " << this->getSourceName(testedSrc);
    // le numéro du bit est calculé modulo 16/32/64 (soit un AND avec 15/31/63)
    _formula << " (bvand (_ bv" << lengthOfSource - 1 << ' ' << lengthOfSource << ") ";
    _formula << this->getSourceName(bitNumberSrc) << "))";

    END_RELATION_DECLARATION;
}
    
void TranslateToSMTLIB::translate_F_PARITY(const TaintPtr &tPtr)
{
    // PARITY : parité de l'octet faible de la variable
    // source http://graphics.stanford.edu/~seander/bithacks.html
    // char v;  v ^= v >> 4;   v &= 0xf;   p = (0x6996 >> v) & 1; 
    //   parité de v = parité de p. 
    //   Si p = 1, parité sera 0 => inverser le résultat (d'ou le bvnot)

    BEGIN_RELATION_DECLARATION;

    // seuls les 8 bits faibles sont considérés
    _formula <<  "\n   let ((t0 ((_ extract 7 0) " << this->getSourceName(tPtr->getSource(0));
    _formula << ")))\n" \
        "  (let ((t1 (bvlshr t0 #x04)))\n" \
        "  (let ((t2 (bvxor t1 t0)))\n" \
        "  (let ((t3 (bvand t2 #x0f)))\n" \
        "  (let ((t4 (bvlshr #x6996 ((_ zero_extend 8) t3))))\n" \
        "  (let ((t5 ((_ extract 0 0) t4)))\n" \
        "  (bvnot t5))))))";

    END_RELATION_DECLARATION;
}
    
void TranslateToSMTLIB::translate_F_IS_NULL(const TaintPtr &tPtr)
{
    ObjectSource src = tPtr->getSource(0);
    UINT32 srcLength = src.getLength();

    BEGIN_RELATION_DECLARATION;

    // comparaison de la source au nombre 0 représenté sur "srcLength" bits
    _formula <<  "ite (= (_ bv0 " << srcLength << ") " << this->getSourceName(src) << ") #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_ARE_EQUAL(const TaintPtr &tPtr)
{
    ObjectSource src0 = tPtr->getSource(0);
    ObjectSource src1 = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;

    // comparaison de la source au nombre 0 représenté sur "srcLength" bits
    _formula <<  "ite (= " << this->getSourceName(src0);
    _formula <<        ' ' << this->getSourceName(src1) << ") #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CMPXCHG_8B16B(const TaintPtr &tPtr)
{
    ObjectSource memHighSrc = tPtr->getSource(0);
    ObjectSource memLowSrc  = tPtr->getSource(1);
    ObjectSource regHighSrc = tPtr->getSource(2);
    ObjectSource regLowSrc  = tPtr->getSource(3);

    BEGIN_RELATION_DECLARATION;

    // comparaison mémoire / registre sur 64 ou 128bits
    _formula <<  "ite (= ";
    _formula << "(concat " << this->getSourceName(memHighSrc) << ' ' << this->getSourceName(memLowSrc) << ") ";
    _formula << "(concat " << this->getSourceName(regHighSrc) << ' ' << this->getSourceName(regLowSrc) << ") ";
    _formula << ") #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_ADD(const TaintPtr &tPtr)
{
    // ADD : Formule reprise à partir de BOCHS 2.6
    // OF(A+B) = MSB de (A XOR RESULT) AND (B XOR RESULT)
    // voir aussi http://www.emulators.com/docs/nx11_flags.htm
    
    ObjectSource srcA   = tPtr->getSource(0);
    ObjectSource srcB   = tPtr->getSource(1);
    ObjectSource sumSrc = tPtr->getSource(2); // forcément marqué
    const std::string sumName(sumSrc.getTaintedSource()->getName());
    UINT32 lengthOfSrc  = srcA.getLength();

    BEGIN_RELATION_DECLARATION;
    
    _formula << "(_ extract " << lengthOfSrc - 1 << ' ' << lengthOfSrc - 1 << ") (bvand";
    // A XOR RESULT
    _formula << "(bvxor " << this->getSourceName(srcA) << ' ' << sumName << ") ";
    // B XOR RESULT 
    _formula << "(bvxor " << this->getSourceName(srcB) << ' ' << sumName << "))";
        
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_SUB(const TaintPtr &tPtr)
{
    // SUB : formule de BOCHS 2.3.5 (BOCHS 2.6 fait différemment)
    // OF(A-B) = MSB de (A XOR RESULT) AND (A XOR B)
    // voir aussi http://www.emulators.com/docs/nx11_flags.htm
    
    ObjectSource srcA   = tPtr->getSource(0);
    ObjectSource srcB   = tPtr->getSource(1);
    ObjectSource sumSrc = tPtr->getSource(2); // forcément marqué
    const std::string sumName(sumSrc.getTaintedSource()->getName());
    UINT32 lengthOfSrc  = srcA.getLength();

    BEGIN_RELATION_DECLARATION;
    
    _formula << "(_ extract " << lengthOfSrc - 1 << ' ' << lengthOfSrc - 1 << ") (bvand ";
    // A XOR RESULT
    _formula << "(bvxor " << this->getSourceName(srcA) << ' ' << sumName << ") ";
    // B XOR RESULT 
    _formula << "(bvxor " << this->getSourceName(srcA) << ' ' << this->getSourceName(srcB) << "))";
        
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_INC(const TaintPtr &tPtr)
{
    // INC déclenche un Overflow ssi la source vaut 0x7f/0x7fff/0x7fffffff/ ...
    // c'est à dire la valeur INT_MAX sur 8, 16, 32 ou 64bits
    ObjectSource src      = tPtr->getSource(0);
    UINT32 lengthOfSource = src.getLength();
    
    BEGIN_RELATION_DECLARATION;
    
    _formula << "ite (= " << src.getTaintedSource()->getName() << " (_ bv";

    switch (lengthOfSource)
    {
    case 8:  _formula << INT8_MAX  << " 8)";  break;
    case 16: _formula << INT16_MAX << " 16)"; break;
    case 32: _formula << INT32_MAX << " 32)"; break;
#if TARGET_IA32E
    case 64: _formula << INT64_MAX << " 64)"; break;
#endif
    }

    _formula << ") #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_DEC(const TaintPtr &tPtr) // NB : NEG IDEM
{
    // DEC (et NEG) déclenche un Overflow ssi la source vaut 0x80/0x8000/0x80000000/ ...
    // c'est à dire la valeur (INT_MAX + 1) sur 8, 16, 32 ou 64bits 
    ObjectSource src      = tPtr->getSource(0);
    UINT32 lengthOfSource = src.getLength();
    
    BEGIN_RELATION_DECLARATION;
    
    _formula << "ite (= " << src.getTaintedSource()->getName() << " (_ bv";

    switch (lengthOfSource)
    {
    case 8:  _formula << static_cast<UINT8>(INT8_MAX) + 1   << " 8)";  break;
    case 16: _formula << static_cast<UINT16>(INT16_MAX) + 1 << " 16)"; break;
    case 32: _formula << static_cast<UINT32>(INT32_MAX) + 1 << " 32)"; break;
#if TARGET_IA32E
    case 64: _formula << static_cast<UINT64>(INT64_MAX) + 1 << " 64)"; break;
#endif
    }

    _formula << ") #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_SHL(const TaintPtr &tPtr)
{
    // Manuel Intel : OF ← MSB(DEST) XOR CF; 
    // en FAIT OF vaut 1 si le signe change apres le déplacmeent
    // ie OF = (MSB "RESULT" == MSB "SOURCE") ? 0 : 1
    // => plus facile à calculer !!!

    ObjectSource beforeShiftSrc = tPtr->getSource(0);
    ObjectSource afterShiftSrc  = tPtr->getSource(1);
    UINT32 msbIndex  = afterShiftSrc.getLength() - 1;
    
    BEGIN_RELATION_DECLARATION;

    _formula << "ite (= ";
    _formula <<   "((_ extract " << msbIndex << ' ' << msbIndex << ") " << this->getSourceName(beforeShiftSrc);
    _formula << ") ((_ extract " << msbIndex << ' ' << msbIndex << ") " << this->getSourceName(afterShiftSrc);
    _formula << ")) #b0 #b1";
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_SHRD(const TaintPtr &tPtr)
{
    // Overflow si le signe change, donc si le LSB du 'bit pattern' et le MSB de l'operande destination
    // sont différents. 1 seule source : la concaténation 'bit Pattern / destination'
    TaintPtr tConcatenatedSrcPtr = tPtr->getSource(0).getTaintedSource(); // forcément marqué
    ObjectSource bitPatternSrc   = tConcatenatedSrcPtr->getSource(0);
    ObjectSource destinationSrc  = tConcatenatedSrcPtr->getSource(1);
    UINT32 msbIndex = destinationSrc.getLength() - 1;

    BEGIN_RELATION_DECLARATION;

    _formula << "ite (= ";
    _formula <<   "((_ extract 0 0) " << this->getSourceName(bitPatternSrc) << ") ";
    _formula <<   "((_ extract " << msbIndex << ' ' << msbIndex << ") " << this->getSourceName(destinationSrc);
    _formula << ")) #b0 #b1";
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_ROL(const TaintPtr &tPtr)
{
    // cf Manuel Intel : OF = MSB(DEST) XOR CF
    ObjectSource resultSrc    = tPtr->getSource(0);
    ObjectSource carryFlagSrc = tPtr->getSource(1);
    UINT32 msbIndex = resultSrc.getLength() - 1;

    BEGIN_RELATION_DECLARATION;

    _formula << "bvxor ((_ extract " << msbIndex << ' ' << msbIndex << ") " << this->getSourceName(resultSrc);
    _formula << ") " << this->getSourceName(carryFlagSrc);

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_OVERFLOW_ROR(const TaintPtr &tPtr)
{
    // cf Manuel Intel : OF = MSB(DEST) XOR ((MSB-1) DEST)
    ObjectSource resultSrc = tPtr->getSource(0);
    UINT32 msbIndex        = resultSrc.getLength() - 1;
    UINT32 msbMinus1Index  = msbIndex - 1; 
    const std::string resultName(resultSrc.getTaintedSource()->getName());

    BEGIN_RELATION_DECLARATION;

    _formula << "bvxor ((_ extract " << msbIndex << ' ' << msbIndex << ") " << resultName << ") ";
    _formula << "((_ extract " << msbMinus1Index << ' ' << msbMinus1Index << ") " << resultName << ')';

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_AUXILIARY_ADD(const TaintPtr &tPtr)
{
    // idem F_CARRY_ADD, mais en considérant les opérandes sur leurs 4 bits les plus faibles
    // On additionne les deux extraits, étendus sur 5 bits, et on prend le bit de poids fort (le 4eme)
    ObjectSource src0  = tPtr->getSource(0);
    ObjectSource src1  = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;

    _formula << "(_ extract 4 4) ";
    _formula << "(bvadd ((_ zero_extend 1) ((_ extract 3 0) " << this->getSourceName(src0) << ")) ";
    _formula <<        "((_ zero_extend 1) ((_ extract 3 0) " << this->getSourceName(src1) << ")))";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_AUXILIARY_NEG(const TaintPtr &tPtr)
{
    BEGIN_RELATION_DECLARATION;
    
    // idem CARRY_NEG mais sur 4 bits : le flag vaut 0 ssi la valeur est nulle (sur 4bits)
    _formula << "ite (= (_ bv0 4) ((_ extract 3 0) " << this->getSourceName(tPtr->getSource(0));
    _formula << ") #b0 #b1";
    
    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_AUXILIARY_SUB(const TaintPtr &tPtr)
{
    ObjectSource src0  = tPtr->getSource(0);
    ObjectSource src1  = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;

    // SUB provoque une retenue si op1 < op2. En SMTLIB utilisation de bvult 
    // qui renvoie true si op 1 < op 2. Pour AF on compare les 4 bits faibles
    _formula << "ite (bvult ((_ extract 3 0) " << this->getSourceName(src0) << ") ";
    _formula <<            "((_ extract 3 0) " << this->getSourceName(src1) << ")) #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_AUXILIARY_INC(const TaintPtr &tPtr)
{
    // retenue provoquée uniquement quand les 4 bits faibles valent 0xf
    BEGIN_RELATION_DECLARATION;

    _formula << "ite (= (_ bv15 4) ((_ extract 3 0) " << this->getSourceName(tPtr->getSource(0)) << ")) #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_AUXILIARY_DEC(const TaintPtr &tPtr)
{
    // retenue provoquée uniquement quand les 4 bits faibles sont nuls
    ObjectSource src0  = tPtr->getSource(0);

    BEGIN_RELATION_DECLARATION;

    _formula << "ite (= (_ bv0 4) ((_ extract 3 0) " << this->getSourceName(src0) << ")) #b1 #b0";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_AAA(const TaintPtr &tPtr)
{
    // condition de AAA : "IF (((AL and 0FH) > 9) or (AF=1)"
    // condition vraie  => flag vaut 1
    // condition fausse => flag vaut 0
    // formule SMT-LIB : 
    // let ((condition (or (bvugt (bvand #x0f src0) #x09) (= src1 #b1)))) 
    //  (ite (= condition true) (bvadd src0 #x01) src0)

    ObjectSource objAL      = tPtr->getSource(0);
    ObjectSource objAuxFlag = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt (bvand #x0f " << this->getSourceName(objAL) << ") #x09) ";
    _formula <<                     "(= " << this->getSourceName(objAuxFlag) << " #b1)))) \n";
    _formula << "(ite (= condition true) #b1 #b0)";

    END_RELATION_DECLARATION;
}

void TranslateToSMTLIB::translate_F_CARRY_DAA_DAS(const TaintPtr &tPtr)
{
    // calcul du carry fait dans la deuxième condition : "IF ((AL > 99H) or (CF = 1))"
    // condition vraie  => flag vaut 1
    // condition fausse => flag vaut 0
    // formule SMT-LIB : 
    // let ((condition (or (bvugt src0 #x99) (= src1 #b1)))) 
    //  (ite (= condition true) #b1 #b0)

    ObjectSource objAL        = tPtr->getSource(0);
    ObjectSource objCarryFlag = tPtr->getSource(1);

    BEGIN_RELATION_DECLARATION;

    _formula << "let ((condition (or (bvugt " << this->getSourceName(objAL) << ") #x99) ";
    _formula <<                     "(= " << this->getSourceName(objCarryFlag) << " #b1)))) \n";
    _formula << "(ite (= condition true) #b1 #b0)";

    END_RELATION_DECLARATION;
}

/////////////////////////////////
// DECLARATION DES CONTRAINTES //
/////////////////////////////////

/*** CONTRAINTES : PREDICAT ***/

std::string TranslateToSMTLIB::getConstraintPredicateHeader(ADDRINT insAddress, PREDICATE p) const
{
    // définition de l'entête de la contrainte : insertion d'un commentaire
    // avec le n° de contrainte, l'instruction et son adresse 
    std::string result(";\n; contrainte " + decstr(_iAssert));
    result += " - "  + hexstr(insAddress);
    result += " - J" + predicateToString[p] + "\n;\n";

    return (result);
}

// formule correspondant au calcul d'un prédicat
std::string TranslateToSMTLIB::getPredicateTranslation(TaintManager_Thread *pTmgrTls, 
    PREDICATE pred, ADDRINT flagsOrRegValue)
{
    // la déclaration d'un prédicat se fait en deux étapes
    // 1) déclaration recursive des objets utilisés dans le calcul du ou des flags concernés
    // 2) construction de l'expression représentant le prédicat
    //    c'est à dire un expression de test sur la valeur du ou des flags
    // Le predicat s'exprime comme un Booléen et porte le nom 'C_' + numéro de contrainte

    std::string result("(define-fun C_" + decstr(_iAssert) + " () Bool (");
    UINT32 oneFlagValue = 0;    // valeur d'un flag (extraction de FlagsOrRegValue)
    
    switch (pred)
    {       
    case PREDICATE_BELOW: 	    // Below (CF==1).
    case PREDICATE_NOT_BELOW: 	// Not Below (CF==0)
        // 1) déclaration récursive des sources du flag
        this->declareObject(pTmgrTls->getTaintCarryFlag());
        
        // 2) construction de l'expression
        result += "= ";
        result += pTmgrTls->getTaintCarryFlag()->getName();
        result += (PREDICATE_BELOW == pred) ? " #b1" : " #b0";
        break;

    case PREDICATE_SIGN:        // Sign (SF==1).
    case PREDICATE_NOT_SIGN :	// Not Sign (SF==0).
        // 1) déclaration récursive des sources du flag
        this->declareObject(pTmgrTls->getTaintSignFlag());
        
        // 2) construction de l'expression
        result += "= ";
        result += pTmgrTls->getTaintSignFlag()->getName();
        result += (PREDICATE_SIGN == pred) ? " #b1" : " #b0";
        break;

    case PREDICATE_ZERO: 	    // Zero (ZF==1).
    case PREDICATE_NOT_ZERO:	// Not Zero (ZF==0).
        // 1) déclaration récursive des sources du flag
        this->declareObject(pTmgrTls->getTaintZeroFlag());
        
        // 2) construction de l'expression
        result += "= ";
        result += pTmgrTls->getTaintZeroFlag()->getName();
        result += (PREDICATE_ZERO == pred) ? " #b1" : " #b0";
        break;

    case PREDICATE_OVERFLOW: 	 // Overflow (OF==1).
    case PREDICATE_NOT_OVERFLOW: // Not Overflow (OF==0)
        // 1) déclaration récursive des sources du flag
        this->declareObject(pTmgrTls->getTaintOverflowFlag());
        
        // 2) construction de l'expression
        result += "= ";
        result += pTmgrTls->getTaintOverflowFlag()->getName();
        result += (PREDICATE_OVERFLOW == pred) ? " #b1" : " #b0";
        break;

    case PREDICATE_PARITY: 	    // Parity (PF==1)
    case PREDICATE_NOT_PARITY: 	// Not Parity (PF==0).
        // 1) déclaration récursive des sources du flag
        this->declareObject(pTmgrTls->getTaintParityFlag());

        // 2) construction de l'expression
        result += "= ";
        result += pTmgrTls->getTaintParityFlag()->getName();
        result += (PREDICATE_PARITY == pred) ? " #b1" : " #b0";
        break;

    case PREDICATE_LESS: 	    // Less (SF!=OF).
    case PREDICATE_NOT_LESS: 	// Greater or Equal (SF==OF).
        result += "ite (= ";

        // insertion SIGN_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isSignFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintSignFlag());
            result += pTmgrTls->getTaintSignFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, SIGN_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        result += ' ';

        // insertion OVERFLOW_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isOverflowFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintOverflowFlag());
            result += pTmgrTls->getTaintOverflowFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, OVERFLOW_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        // si egaux, flag vaut 0 dans cas LESS et 1 dans cas NOT_LESS
        result += (PREDICATE_LESS == pred) ? ") false true" : ") true false";
        break;

    case PREDICATE_BELOW_OR_EQUAL: 	    // Below or Equal (CF==1 or ZF==1), ou (CF or ZF) == 1
    case PREDICATE_NOT_BELOW_OR_EQUAL: 	// Above (CF==0 and ZF==0), ou (CF or ZF) == 0
        // calcul et test de la valeur du OR entre les deux flags
        result += "= (bvor ";

        // insertion CARRY_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isCarryFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintCarryFlag());
            result += pTmgrTls->getTaintCarryFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, CARRY_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        result += ' ';

        // insertion ZERO_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isZeroFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintZeroFlag());
            result += pTmgrTls->getTaintZeroFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, ZERO_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        // BELOW_OR_EQUAL: le flag vaut 1 si le 'OR' vaut 1
        result += (PREDICATE_BELOW_OR_EQUAL == pred) ? ") #b1" : ") #b0";
        break;

    case PREDICATE_LESS_OR_EQUAL: // Less or Equal (ZF==1 or SF!=OF), ou ((SF ^ OF) or ZF) == 1
    case PREDICATE_NOT_LESS_OR_EQUAL: // Greater (ZF==0 and SF==OF),  ou ((SF ^ OF) or ZF) == 0
        // calcul et test de la valeur du OR entre (bvxor SF OF) et ZF
        result += "= (bvor (bvxor ";

        // insertion SIGN_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isSignFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintSignFlag());
            result += pTmgrTls->getTaintSignFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, SIGN_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        result += ' ';

        // insertion OVERFLOW_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isOverflowFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintOverflowFlag());
            result += pTmgrTls->getTaintOverflowFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, OVERFLOW_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        result += ") ";

        // insertion ZERO_FLAG : objet ou valeur selon marquage
        if (pTmgrTls->isZeroFlagTainted())
        {
            // 1) déclaration récursive des sources du flag
            this->declareObject(pTmgrTls->getTaintZeroFlag());
            result += pTmgrTls->getTaintZeroFlag()->getName();
        }
        else
        {
            oneFlagValue = EXTRACTBIT(flagsOrRegValue, ZERO_FLAG);
            result      += (oneFlagValue) ? "#b1" : "#b0";
        }

        // LESS_OR_EQUAL: le flag vaut 1 si le 'OR' vaut 1
        result += (PREDICATE_LESS_OR_EQUAL == pred) ? ") #b1" : ") #b0";
        break;

    case PREDICATE_CX_NON_ZERO: 	// CX != 0.
        {
            // récupération de l'objet représentant CX, et déclaration de celui-ci
            TaintWordPtr regCXPtr = pTmgrTls->getRegisterTaint<16>(REG_CX, flagsOrRegValue);
            this->declareObject(regCXPtr);

            // insertion de nom de l'objet, maintenant qu'il est déclaré, et comparaison à 0
            result += "not (= " + regCXPtr->getName() + " (_ bv0 16))";
            break;
        }

    case PREDICATE_ECX_NON_ZERO: 	// ECX != 0.
        {
            // récupération de l'objet représentant ECX, et déclaration de celui-ci
            TaintDwordPtr regECXPtr = pTmgrTls->getRegisterTaint<32>(REG_ECX, flagsOrRegValue);
            this->declareObject(regECXPtr);

            // insertion de nom de l'objet, maintenant qu'il est déclaré, et comparaison à 0
            result += "not (= " + regECXPtr->getName() + " (_ bv0 32))";
            break;
        }
#if TARGET_IA32E
    case PREDICATE_RCX_NON_ZERO: 	// RCX != 0.
        {
            // récupération de l'objet représentant RCX, et déclaration de celui-ci
            TaintQwordPtr regRCXPtr = pTmgrTls->getRegisterTaint<64>(REG_RCX, flagsOrRegValue);
            this->declareObject(regRCXPtr);

            // insertion de nom de l'objet, maintenant qu'il est déclaré, et comparaison à 0
            result += "not (= " + regRCXPtr->getName() + " (_ bv0 64))";
            break;
        }
#endif
    }
    // fin de ligne = fermeture des parenthèses
    result += ")); ";
    if (g_verbose) result += predicateToString[pred];
    result += '\n';

    return (result);
} // getPredicateFormula
 
std::string TranslateToSMTLIB::getConstraintPredicateFooter(bool taken) const
{
    // déclaration de l'assertion en fin de contrainte 
    // selon que la branche a été prise ou non
    std::string result("(assert (= C_" + decstr(_iAssert));
    result += taken ? " true" : " false";
    result += "))\n";

    return (result);
} // addConstraintJcc


/*** CONTRAINTES : DIVISEUR NUL ***/

// déclaration de l'entête d'une nouvelle contrainte pour un diviseur nul
std::string TranslateToSMTLIB::getConstraintNullDivisorHeader(ADDRINT insAddress) const
{ 
    // définition de l'entête de la contrainte : insertion d'un commentaire
    // avec le n° de contrainte, l'instruction et son adresse 
    return (";\n; contrainte " + decstr(_iAssert) \
         + " - " + hexstr(insAddress) + " - DIVISION avec Diviseur Marqué\n;\n");
}

// renvoie la traduction de la formule imposant un diviseur nul
std::string TranslateToSMTLIB::getNullDivisorTranslation(const TaintPtr &divisorPtr)
{ 
    // déclaration de l'objet représentant le diviseur et de ses sources
    this->declareObject(divisorPtr);
    
    // déclaration de la contrainte sur la nullité du diviseur
    std::string result("(define-fun C_" + decstr(_iAssert) + " () Bool ");
    result += "(= (_ bv0 " + decstr(divisorPtr->getLength()) + ") " + divisorPtr->getName() + "))\n";

    return (result);
}

// déclaration du 'final' d'une contrainte pour un diviseur nul
std::string TranslateToSMTLIB::getConstraintNullDivisorFooter() const
{ 
    // déclaration de l'assertion en fin de contrainte : à l'exécution le diviseur
    // est forcément non nul, sinon il y aurait crash !!
    return ("(assert (= C_" + decstr(_iAssert) + " false))\n");
}

/*** CONTRAINTES : QUOTIENT DIVISION HORS BORNES ***/

// déclaration de l'entête d'une nouvelle contrainte sur le résultat d'une division
std::string TranslateToSMTLIB::getConstraintDivOverflowHeader(bool isSignedDivision, ADDRINT insAddress) const
{
    // définition de l'entête de la contrainte : insertion d'un commentaire
    // avec le n° de contrainte, l'instruction et son adresse 
    return (";\n; contrainte " + decstr(_iAssert) + " - " + hexstr(insAddress) \
        + " - DIVISION " + (isSignedDivision ? "signée" : "non signée") + "\n;\n");
}

// renvoie la traduction de la formule sur le résultat d'une division
std::string TranslateToSMTLIB::getDivOverflowTranslation(bool isSignedDivision, const TaintPtr& quotientPtr)
{ 
    ObjectSource objHighDividend = quotientPtr->getSource(0);
    ObjectSource objLowDividend  = quotientPtr->getSource(1);
    ObjectSource objDivisor      = quotientPtr->getSource(2);
    UINT32       divisorLength   = objDivisor.getLength();

    // déclaration des operandes et de leurs sources
    if (objHighDividend.isSrcTainted()) this->declareObject(objHighDividend.getTaintedSource());
    if (objLowDividend.isSrcTainted())  this->declareObject(objLowDividend.getTaintedSource());
    if (objDivisor.isSrcTainted())      this->declareObject(objDivisor.getTaintedSource());

    // déclaration de la contrainte sur les bornes du resultat
    std::string result("(define-fun C_" + decstr(_iAssert) + " () Bool (");
    // concaténation du dividende
    std::string dividend("(concat " + this->getSourceName(objHighDividend) + ' ' + this->getSourceName(objLowDividend) + ')');
    
    // cas division signée : resultat en dehors de [80h ; 7fh] pour provoquer un overflow
    if (isSignedDivision)
    {
        std::string lowBound, highBound;
        switch (divisorLength)
        {
        case 8:  lowBound = "#xFF80"; highBound = "#x007f"; break;
        case 16: lowBound = "#xFFFF8000"; highBound = "#x00007fff"; break;
        case 32: lowBound = "#xFFFFFFFF80000000"; highBound = "#x000000007fffffff"; break;
#if TARGET_IA32E
        case 64: 
            lowBound  = "#xFFFFFFFFFFFFFFFF8000000000000000"; 
            highBound = "#x00000000000000007fffffffffffffff"; 
            break;
#endif
        default : return "";
        }
        
        result += "let ((temp (bvsdiv " + dividend + " ((_ sign_extend " + decstr(divisorLength) + ") ";
        result += this->getSourceName(objDivisor) + ")))) ";
        result += "(or (bvsgt temp " + highBound + ") (bvslt temp " + lowBound + "))))\n";
    }

    // cas division non signée : resultat supérieur à FF / FFFF / ... pour provoquer un overflow
    else
    {
        std::string highBound;
        switch (divisorLength)
        {
        case 8:  highBound = "#x00ff"; break;
        case 16: highBound = "#x0000ffff"; break;
        case 32: highBound = "#x00000000ffffffff"; break;
#if TARGET_IA32E
        case 64: highBound = "#x0000000000000000ffffffffffffffff"; break;
#endif
        default : return "";
        }
        
        result += "let ((temp (bvudiv " + dividend + " ((_ zero_extend " + decstr(divisorLength) + ") ";
        result += this->getSourceName(objDivisor) + ")))) ";
        result += "(bvugt temp " + highBound + ")))\n";
    }

    return (result);
}

// déclaration du 'final' d'une contrainte sur le résultat d'une division
std::string TranslateToSMTLIB::getConstraintDivOverflowFooter() const
{ 
    // déclaration de l'assertion en fin de contrainte 
    // à l'exécution le résultat est forcément dans les bornes, sinon il y aurait crash !!
    return ("(assert (= C_" + decstr(_iAssert) + " false))\n"); 
}


/*** CONTRAINTES : BOUCLES (LOOP/LOOPE/LOOPNE) ***/

// déclaration de l'entête d'une nouvelle contrainte pour un diviseur nul
std::string TranslateToSMTLIB::getConstraintLoopHeader(ADDRINT insAddress) const
{
    // définition de l'entête de la contrainte : insertion d'un commentaire
    // avec le n° de contrainte, l'instruction et son adresse 
    std::string result(";\n; contrainte " + decstr(_iAssert));
    result += " - "  + hexstr(insAddress);
    result += " - LOOP\n;\n";

    return (result);
}

// renvoie la traduction de la formule relatif à une boucle Loop (LOOP)
std::string TranslateToSMTLIB::getLoopTranslation(const TaintPtr &regCounterPtr)
{    
    // déclaration de l'objet représentant le registre compteur
    this->declareObject(regCounterPtr);

    // déclaration de la contrainte : le compteur doit être non nul
    std::string result("(define-fun C_" + decstr(_iAssert) + " () Bool (");
    
    result += "not (= (_bv0 " + decstr(regCounterPtr->getLength()) + ") ";
    result += regCounterPtr->getName() + ")))\n";

    return (result);
}

// renvoie la traduction de la formule relatif à une boucle Loop (LOOPE/LOOPNE)
std::string TranslateToSMTLIB::getLoopTranslation(PREDICATE pred, 
    const ObjectSource &objRegCounter, const ObjectSource &objZF)
{
    // déclaration de l'objet représentant le registre compteur et Zero Flag, si marqués
    if (objRegCounter.isSrcTainted()) this->declareObject(objRegCounter.getTaintedSource());
    if (objZF.isSrcTainted())         this->declareObject(objZF.getTaintedSource());

    std::string result("(define-fun C_" + decstr(_iAssert) + " () Bool (");
    
    // déclaration de la contrainte : deux conditions
    result += "and";
    // le compteur doit être non nul
    result +=       " (not (= (_ bv0 " + decstr(objRegCounter.getLength()) + ") ";
    result +=       this->getSourceName(objRegCounter) + "))";
    // et le zeroFlag vaut 1 (cas LOOPE) ou 0 (cas LOOPNE)
    result +=       " (= " + this->getSourceName(objZF) + " #b";
    result +=         (PREDICATE_ZERO == pred) ? '1' : '0';
    result +=       ")))\n";

    return (result);
}

// déclaration du 'final' d'une contrainte sur le résultat d'une division
std::string TranslateToSMTLIB::getConstraintLoopFooter() const
{
    // déclaration de l'assertion en fin de contrainte 
    // pour les boucles, la contrainte est vraie car la branche a été prise
    return ("(assert (= C_" + decstr(_iAssert) + " true))\n"); 
}

/*** CONTRAINTES : ADRESSES EFFECTIVES ***/

// déclaration de l'entête d'une nouvelle contrainte sur une addresse
std::string TranslateToSMTLIB::getConstraintAddressHeader(ADDRINT insAddress) const
{
    // définition de l'entête de la contrainte : insertion d'un commentaire
    // avec le n° de contrainte, l'instruction et son adresse 
    return (";\n; contrainte " + decstr(_iAssert) + " - " + hexstr(insAddress) + " - ADDRESSE MARQUEE\n;\n");
}

// renvoie la traduction de la formule sur la valeur d'une adresse
std::string TranslateToSMTLIB::getConstraintAddressTranslation(const TaintPtr &addrPtr, ADDRINT addrValue)
{ 
    // déclaration de l'objet te de ses sources
    this->declareObject(addrPtr);

    // déclaration de la contrainte sur la valeur du résultat
    std::string result("(define-fun C_" + decstr(_iAssert) + " () Bool (");
    // valeur concrète de l'adresse
    result += "= (_ bv" + decstr(addrValue) + ' ' + decstr(addrPtr->getLength()) + ") ";
    // nom de la variable
    result += addrPtr->getName() + "))";

    if (g_verbose) result += "; ADDRESSE MARQUEE";

    result += '\n';

    return (result);
}

// déclaration du 'final' d'une contrainte sur le résultat d'une division
std::string TranslateToSMTLIB::getConstraintAddressFooter() const
{ 
    // déclaration de l'assertion en fin de contrainte 
    // à l'exécution la variable marquée vaut l'adresse réelle
    return ("(assert (= C_" + decstr(_iAssert) + " true))\n"); 
}


// envoi des denières données : nombre total de contraintes
void TranslateToSMTLIB::final() 
{
    WINDOWS::DWORD cbWritten = 0;
    std::string finalFormula;
    
    if (g_nopipe)
    {
        // option 'nopipe' : construction d'une formule "prete à l'emploi"
        // avec insertion de la logique, et des commandes "check-sat" et "get-model" 
        std::string formulaHeader =
            ";*********************************\n"     \
            ";*** FUZZWIN " + FUZZWIN_VERSION + "***\n"\
            ";***        MODE NO PIPE       ***\n"     \
            ";*********************************\n"     \
            "; Fichier instrumenté : " + g_inputFile + "\n\n";

        formulaHeader +=
            "(set-option :auto-config true)\n" \
            "(set-logic QF_AUFBV)\n";

        std::string formulaFooter = 
            "(check-sat)\n" \
            "(get-model)\n";

        finalFormula = formulaHeader + _formula.str() + formulaFooter;
    }
    else
    {
        // option pipe : insertion du nombre total de contraintes 
        _formula << ";@" << std::dec << _iAssert;
        finalFormula = _formula.str();
    }

    // envoi de la formule en entier dans le pipe (ou fichier en mode debug)
    WINDOWS::WriteFile(g_hPipe, 
        finalFormula.c_str(), 
        static_cast<WINDOWS::DWORD>(finalFormula.size()), // pour eviter C4267 en x64 
        &cbWritten, 
        NULL);
    WINDOWS::FlushFileBuffers(g_hPipe);
}
