#include "buildFormula.h"

// CONSTRUCTEUR
SolverFormula::SolverFormula(): 
    m_iAssert(0), // valeur nulle mais la première contrainte sera la n°1 (cf fonction declareHeader)
    m_iTbit(0), m_iTb(0), m_iTw(0), m_iTdw(0), m_iTqw(0), m_iTdqw(0),
    m_formula(std::ostringstream::ate)
{}

// nom de variable pour les objets, utilisées dans les formules SMTLIB
void SolverFormula::insertSourceName(std::string &out, const ObjectSource &objSrc) 
{
    // si objet marqué, récupérer son nom de variable
    if (objSrc.isSrcTainted())	 out += objSrc.getTaintedSource()->getName(); 
    // sinon fabrication de la valeur, en format SMTLIB
    else 
    {
        UINT32 srcLength = objSrc.getLength(); // longueur de l'objet (en bits)
        ADDRINT value =  objSrc.getValue(); // valeur numérique représentée par l'objet
        
        // cas TaintBit : résultat décrit en binaire
        if (srcLength == 1)	out += value ? "#b1" : "#b0";
        // dans les autres cas : resultat en hexa
        else
        {
            // la fonction StringFromAddrint (API PIN) convertit un ADDRINT(32 ou 64bits) 
            // en chaine de caractères. Or la source est encodée sur 'srcLength' bits
            // donc extraire les 2/4/8/16 derniers chiffres, selon la taille
            std::string valueString(StringFromAddrint(value));
            out += "#x";
            out += valueString.substr(valueString.size() - (srcLength >> 2)); 
        }
    }
} // insertSourceName

////////////////////////////////////
// DECLARATION DES OBJETS MARQUES //
////////////////////////////////////

void SolverFormula::declareObject(const TaintPtr &tPtr) 
{
    // traitement uniquement si la variable n'a jamais été déclarée 
    if ( !tPtr->isDeclared()) 
    {
        // déclaration de la variable
        tPtr->setDeclared();

        // récupération des sources, et déclarations récursives de celles ci
        auto sources = tPtr->getSources();
        for (auto it = sources.begin() ; it != sources.end() ; ++it) 
        {
            if ((*it).isSrcTainted()) declareObject((*it).getTaintedSource());
        }

        // Maintenant que les sources sont déclarées, déclaration de l'objet
        // récupération de la relation de l'objet
        Relation rel = tPtr->getSourceRelation();
        
        if (rel == X_ASSIGN) 
        {
            // on affecte à l'objet le nom de la source
            // cela evite de déclarer une nouvelle variable dans le solveur 
            tPtr->setName(sources.front().getTaintedSource()->getName()); 
        }
        else if (rel == BYTESOURCE) 
        {	
            // déclaration du nom de variable
            std::string objectName("OFF");
            objectName += decstr(sources.front().getValue());
            tPtr->setName(objectName);

            // enregistrement dans la formule
            this->m_formula << "(declare-const " << objectName << " (_ BitVec 8))\n";
        }
       
        // relation née d'une instruction x86 ou d'un marquage de flag
        else this->declareRelation(tPtr, sources); 
    } 
} // declareObject

///////////////////////////////
// DECLARATION DES RELATIONS //
///////////////////////////////

void SolverFormula::declareRelation(const TaintPtr &tPtr, const vector<ObjectSource> &sources)
{
    UINT32 lengthOfResult = tPtr->getLength();  // longueur du résultat 
    Relation rel = tPtr->getSourceRelation();   // relation résultat <-> sources
    
    // fabrication du nom de variable unique selon la taille du resultat
    std::string name; 
    switch (lengthOfResult) 
    {
    case 1:	 name = "TBIT"  + decstr(++(this->m_iTbit));  break;
    case 8:	 name = "TB"    + decstr(++(this->m_iTb));  break;
    case 16: name = "TW"    + decstr(++(this->m_iTw));  break;
    case 32: name = "TDW"   + decstr(++(this->m_iTdw)); break;
    case 64: name = "TQW"   + decstr(++(this->m_iTqw)); break;
    case 128: name = "TDQW" + decstr(++(this->m_iTdqw)); break;
    default : name = "error"; break;
    }
    // Affectation du nom à l'objet
    tPtr->setName(name);

    // declaration de l'entête de ligne : nom de variable
    std::string out("(define-fun " + name + " () (_ BitVec " + decstr(lengthOfResult) + ") ");

    // insertion des arguments selon la relation
    /****** MEGA BIG SWITCH ;););););); *****/
    switch (rel) 
    {
    case EXTRACT: 
    {
        // taille destination = taille de l'intervalle d'extraction (moins 1)
        UINT32 indexOfExtraction = static_cast<UINT32>(sources[1].getValue());

        // borne min = index d'extraction * longueur
        UINT32 lowerLimit = indexOfExtraction * lengthOfResult;
        // borne max = borne min + (longueur - 1)
        UINT32 higherLimit = lowerLimit + (lengthOfResult - 1);

        out += "((_ extract ";
        out += decstr(higherLimit);
        out += ' ';
        out += decstr(lowerLimit);
        out += ") ";     

        // ajout de l'objet subissant l'extraction
        out += sources.front().getTaintedSource()->getName();
        break;
    }		
    case CONCAT:	
    {    
        // CONCAT : concaténation des objets fournis en Sources
        // Attention : les objets seront inséres du plus fort au plus faible
        // d'ou le rbegin/rend (cf def CONCAT du langage SMTLIB)

        out += "(concat";
        for (auto it = sources.rbegin();  it != sources.rend() ; ++it) 
        {
            out += ' ';
            this->insertSourceName(out, *it);
        } 
        break;
    }
    case X_SIGNEXTEND:	
    {
        // nombre de bits à ajouter = longueur resultat - longueur source
        UINT32 lengthExtension = lengthOfResult - sources.front().getLength();

        out += "((_ sign_extend ";
        out += decstr(lengthExtension);
        out += ") ";

        // insertion du nom de l'objet
        this->insertSourceName(out, sources.front());
        break;
    }  
    case X_ADD:
    {
        out += "(bvadd ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        break;
    }
    case X_SUB:
    {
        out += "(bvsub ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        break;
    }
    case X_AND:
    {
        out += "(bvand ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        break;
    }
    case X_OR:
    {
        out += "(bvor ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        break;
    }
    case X_XOR:
    {
        out += "(bvxor ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        break;
    }
    case X_INC:
    case X_DEC:
    {
        out += (rel == X_INC) ? "(bvadd " : "(bvsub ";
        out += sources.front().getTaintedSource()->getName();
        out += " (_ bv1 " + decstr(lengthOfResult) + ')';
        break;
    }
    case X_NEG:	
    case X_NOT:
    {
        out += (rel == X_NEG) ? "(bvneg " : "(bvnot ";
        this->insertSourceName(out, sources.front());
        break;
    }
    case X_SHL:
    case X_SHR:
    case X_SAR:
    {
        out += (rel == X_SHL) ? "(bvshl " : ((rel == X_SHR) ? "(bvlshr " : "(bvashr ");
        this->insertSourceName(out, sources.front());
        out += ' ';

        // si le décalage est non marqué : il a déjà été masqué dans l'analyse
        // insertion du décalage au format décimal
        if (!sources[1].isSrcTainted())
        {
            out += "(_ bv";
            out += decstr(sources[1].getValue());
            out += ' ';
            out += decstr(lengthOfResult);
            out += ')';
        } 
        else // si décalage marqué (8bits) : masquage à 0x1f (ou 0x3f si 64 bits)
        {
            if (lengthOfResult != 8) // ajustement à la longueur de la source décalée
            {  
                out += "((_ zero_extend ";
                out += decstr(lengthOfResult - 8);
                out += ") ";
            }
            out += "(bvand ";
            out += sources[1].getTaintedSource()->getName();
            out += (lengthOfResult == 64) ? " #x3f)" : " #x1f)";
            // si utilisation de zero_ext : parenthèse fermante en +
            if (lengthOfResult != 8)   out += ')'; 
        }
        break;
    }
    case X_ROR:
    {
        // src 0 = objet qui subit le décalage (marqué ou non), src 1 = décalage (marqué ou non)
        
        // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_right'
        if (!sources[1].isSrcTainted())
        {
            out += "((_ rotate_right ";
            out += decstr(sources[1].getValue());
            out += ") ";
            this->insertSourceName(out, sources.front());
        }
        // si depl marqué, obligation de passer par deux shifts (cf _rotr de stblib.h)
        else
        {
            // _rotr(val, depl) = (val >> depl) | (val << (sizeof(val) * 8 - depl))
            // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
            // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend si necessaire
            const std::string adjustLengthForShift = (lengthOfResult == 8) 
                ? "" : ("((_ zero_extend " + decstr(lengthOfResult - 8) + ") ");

            // masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
            out += "(let ((m_depl (bvand ";
            out += sources[1].getTaintedSource()->getName();  // objet représentant le déplacement
            out += (lengthOfResult == 64) ? " #x3f" : " #x1f";

            // (val >> s) |
            out += "))) (bvor (bvlshr ";
            // objet subissant la rotation, marqué ou non
            this->insertSourceName(out, sources.front()); 
            out += ' ';
            out += adjustLengthForShift;
            out += "m_depl)) (bvshl ";

            // (val << (sizeof(val) * 8 - s)) <=> bvshl(rotSrc((_ ze bvsub (lengthOfResult deplSrc)) 
            this->insertSourceName(out, sources.front());
            out += ' ';
            out += adjustLengthForShift;
            out += "(bvsub (_ bv";
            out += decstr(lengthOfResult);
            out += " 8) m_depl))))";
        }
        break;
    }
    case X_ROL: 
    {
        // src 0 = objet qui subit le décalage (marqué ou non), src 1 = décalage (marqué ou non)
        
        // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_left'
        if (!sources[1].isSrcTainted())
        {
            out += "((_ rotate_left ";
            out += decstr(sources[1].getValue());
            out += ") ";
            this->insertSourceName(out, sources.front());
        }
        // si depl marqué, obligation de passer par deux shifts (cf _rotl de stblib.h)
        else
        {
            // _rotl(val, s) = (val << s) | (val >> (sizeof(val) * 8 - s))
            // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
            // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend si nécessaire
            const std::string adjustLengthForShift = (lengthOfResult == 8) 
                ? "" : ("((_ zero_extend " + decstr(lengthOfResult - 8) + ") ");

            // masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
            out += "(let ((m_depl (bvand ";
            out += sources[1].getTaintedSource()->getName();  // objet représentant le déplacement
            out += (lengthOfResult == 64) ? " #x3f" : " #x1f";

            // (val >> s) |
            out += "))) (bvor (bvshl ";
            // objet subissant la rotation, marqué ou non
            this->insertSourceName(out, sources.front());
            out += ' ';
            out += adjustLengthForShift;
            out += "m_depl)) (bvlshr ";

            // (val << (sizeof(val) * 8 - s)) <=> bvshl(rotSrc((_ ze bvsub (lengthOfResult deplSrc)) 
            this->insertSourceName(out, sources.front());
            out += ' ';
            out += adjustLengthForShift;
            out += "(bvsub (_ bv";
            out += decstr(lengthOfResult);
            out += " 8) m_depl))))";
        }
        break;
    }
    case X_RCR: 
    {
        // idem dans l'approche que pour ROR, sauf que la source est ici la concaténation 
        // de sources[0](source) avec sources[1](CarryFlag) 
        // => obligation de faire toutes les operations (bvshl, bvsub, ... ) sur (len + 1 bits)
        // et au final d'extraire les 'len' bits forts

        out += "((_ extract ";
        out += decstr(lengthOfResult);
        out += " 1)";

        // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_right'
        if (!sources[2].isSrcTainted())
        {
            out += "((_ rotate_right ";
            out += decstr(sources[2].getValue());

            // concatenation de la source avec le carryFlag
            out += ") (concat ";
            this->insertSourceName(out, sources.front());
            out += ' ';
            this->insertSourceName(out, sources[1]);
            out += "))";
        }
        // si depl marqué, obligation de passer par deux shifts (cf _rotr de stblib.h)
        else
        {
            // _rotr(val, s) = (val >> s) | (val << (sizeof(val) * 8 - s))
            // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
            // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend à len+1 bits
            const std::string adjustLengthForShift
                ("((_ zero_extend " + decstr(lengthOfResult - 7) + ") ");

            // masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
            out += "(let ((m_depl (bvand ";
            out += sources[2].getTaintedSource()->getName();  // objet représentant le déplacement
            out += (lengthOfResult == 64) ? " #x3f" : " #x1f";

            // construction de la concatenation source/carry Flag
            out += ")) (src_cf (concat ";
            this->insertSourceName(out, sources.front());
            out += ' ';
            this->insertSourceName(out, sources[1]);

            // (val >> s) | (val << (sizeof(val) * 8 - s)) 
            out += "))) (bvor (bvlshr src_cf ";
            out += adjustLengthForShift;
            out += "m_depl)) (bvshl src_cf ";

            out += adjustLengthForShift;
            out += "(bvsub (_ bv";
            out += decstr(lengthOfResult);
            out += " 8) m_depl)))))";
        }
        break;
    }
    case X_RCL:
    {
        // idem dans l'approche que pour ROL, sauf que la source est ici la concaténation 
        // de sources[0](source) avec sources[1](CarryFlag) : (CF)(Src0)
        // => obligation de faire toutes les operations (bvshr, bvsub, ... ) sur (len + 1 bits)
        // et au final d'extraire les 'len' bits faibles

        out += "((_ extract ";
        out += decstr(lengthOfResult - 1);
        out += " 0)";

        // si déplacement non marqué : utilisation de l'instruction SMTLIB '_ rotate_left'
        if (!sources[2].isSrcTainted())
        {
            out += "((_ rotate_left ";
            out += decstr(sources[2].getValue());
            
            // concatenation de la source avec le carryFlag
            out += ") (concat ";
            this->insertSourceName(out, sources.front());
            out += ' ';
            this->insertSourceName(out, sources[1]);
            out += "))";
        }
        // si depl marqué, obligation de passer par deux shifts (cf _rotl de stblib.h)
        else
        {
            // _rotl(val, s) = (val << s) | (val >> (sizeof(val) * 8 - s))
            // comme pour shift, obligation de mettre l'objet "depl" (sur 8 bits) 
            // à la meme longueur que l'objet déplacé : utilisation de ZeroExtend
            const std::string adjustLengthForShift
                ("((_ zero_extend " + decstr(lengthOfResult - 7) + ") ");

            // masquage du déplacement à 0x1f (ou 0x3f en 64 bits)
            out += "(let ((m_depl (bvand ";
            out += sources[2].getTaintedSource()->getName();  // objet représentant le déplacement
            out += (lengthOfResult == 64) ? " #x3f" : " #x1f";
            
            // construction de la concatenation source/carry Flag
            out += ")) (src_cf (concat ";
            this->insertSourceName(out, sources.front());
            out += ' ';
            this->insertSourceName(out, sources[1]);
            
            // (val << s) | (val >> (sizeof(val) * 8 - s)) 
            out += "))) (bvor (bvshl src_cf ";
            out += adjustLengthForShift;
            out += "m_depl)) (bvlshr src_cf ";
            
            out += adjustLengthForShift;
            out += "(bvsub (_ bv";
            out += decstr(lengthOfResult);
            out += " 8) m_depl)))))";
        }
        break;
    }
    case X_COMPLEMENT_BIT:
    case X_SET_BIT:
    {
        // COMPLEMENT : XOR de la source avec (1<<numero bit)
        // SET : OR de la source avec (1<<numero bit)
        // position du bit calculée modulo 16/32/64 (soit un AND avec 15/31/63)
        // ie (bvor/bvxor 'src0' (bvshl (_bv1 'srcLen') (bvand 'src1' (_bv15/31/63 'srcLen')))
       
        UINT32 srcLength = sources.front().getLength(); // nombre de bits de la source
        const std::string srcLengthName(decstr(srcLength)); // représentation en string

        out += (rel == X_SET_BIT) ? "(bvor " : "(bvxor ";
        this->insertSourceName(out, sources.front());

        out += " (bvshl (_ bv1 ";
        out += srcLengthName; // nombre 1 sur x bits
        out += ") (bvand ";
        this->insertSourceName(out, sources[1]);

        // nombre 15/31/64 sur 'len' bits
        out += " (_ bv";
        out += decstr(srcLength - 1);
        out += ' ';
        out += srcLengthName;
        out += ")))";
        break;
    }
    case X_CLEAR_BIT:
    {
        // AND de la source avec ~(1<<numero bit)
        // position du bit calculée modulo 16/32/64 (soit un AND avec 15/31/63)
        // ie (bvand 'src0' (bvnot (bvshl (_bv1 'srcLen') (bvand 'src1' (_bv15/31/63 'srcLen'))))
       
        UINT32 srcLength = sources.front().getLength(); // nombre de bits de la source
        const std::string srcLengthName(decstr(srcLength)); // représentation en string

        out += "(bvand ";
        this->insertSourceName(out, sources.front());

        out += " (bvnot (bvshl (_ bv1 ";
        out += srcLengthName; // nombre 1 sur x bits
        out += ") (bvand ";
        this->insertSourceName(out, sources[1]);

        // nombre 15/31/64 sur 'len' bits
        out += " (_ bv";
        out += decstr(srcLength - 1);
        out += ' ';
        out += srcLengthName;
        out += "))))";
        break;
    }
    case X_IMUL:
    {  
        // longueur resultat = 2*longueur des sources 
        // donc necessite de mettre les opérandes à la longueur de
        // la destination ; le nombre de zéros à ajouter est égal à 
        // la longueur de la source (= moitié longueur du résultat)
        const std::string zeroExtend("((_ zero_extend " + decstr(lengthOfResult >> 1) + ") ");

        out += "(bvmul ";
        // 1ere source, zero-étendue
        out += zeroExtend;
        this->insertSourceName(out, sources.front());
        out += ") ";
        // 2eme source, zero-étendue
        out += zeroExtend;
        this->insertSourceName(out, sources[1]);
        out += ')';
    
        break;
    }
    case X_DIV_QUO:
    case X_DIV_REM:
    case X_IDIV_QUO:
    case X_IDIV_REM:
    {
        // taille resultat = taille diviseur = 1/2 taille dividende
        // il faut donc effectuer "Dividende / zero_extend(diviseur)" 
        // et en extraire la partie basse pour obtenir 
        // le résultat (DIV_QUO) ou le reste (DIV_REM)
        // Src 0 : dividende (entier si 8 bits, sinon partie haute)
        // Src 1 : dividende (partie basse) ou diviseur (si 8 bits)
        // Src 2 : diviseur (si différent 8 bits), sinon rien
        const std::string instruction( 
                       (rel == X_DIV_QUO) ? "(bvudiv "
                    : ((rel == X_DIV_REM) ? "(bvurem "
                    : ((rel == X_IDIV_QUO) ? "(bvsdiv "
                    : "(bvsrem ")));

        out += "((_ extract ";
        switch (lengthOfResult)
        {
        case 8: // resultat 8bits : dividende en src0, diviseur 8b en src 1
            out += "7 0) ";
            out += instruction;
            
            // dividende (16 bits) - source 0
            this->insertSourceName(out, sources.front());    

            // extension sur 16 bits du diviseur (8 bits) - source 1
            out += " ((_ zero_extend 8) ";       
            this->insertSourceName(out, sources[1]);
            break;
        // Autres longueurs => Source0 : partie forte du dividende
        // Source1 : partie faible du dividende
        // Source2 : diviseur
        case 16:
            // extraction de la partie faible de la division
            out += "15 0) " ;
            out += instruction;

            // division : concaténation du dividende (sources 0 et 1)
            out += "(concat ";
            this->insertSourceName(out, sources.front());          
            out += ' ';
            this->insertSourceName(out, sources[1]); 

            // extension du diviseur à la longueur du dividende
            out += ") ((_ zero_extend 16) ";
            this->insertSourceName(out, sources[2]);
            break;
        case 32:
            // extraction de la partie faible de la division
            out += "31 0) " ;
            out += instruction;

            // division : concaténation du dividende (sources 0 et 1)
            out += "(concat ";
            this->insertSourceName(out, sources.front());          
            out += ' ';
            this->insertSourceName(out, sources[1]);

            // extension du diviseur à la longueur du dividende
            out += ") ((_ zero_extend 32) ";
            this->insertSourceName(out, sources[2]);
            break;
        #if TARGET_IA32E
        case 64:
            // extraction de la partie faible de la division
            out += "63 0) " ;
            out += instruction;

            // division : concaténation du dividende (sources 0 et 1)
            out += "(concat ";
            this->insertSourceName(out, sources.front());          
            out += ' ';
            this->insertSourceName(out, sources[1]); 

            // extension du diviseur à la longueur du dividende
            out += ") ((_ zero_extend 64) ";
            this->insertSourceName(out, sources[2]);
            break;
        #endif
        }
        // fin de formule
        out += "))";
        break;
    }
                    
    /*************************************/
    /************ FLAGS ******************/
    /*************************************/

    case F_LSB:	
    {
        out += "((_ extract 0 0) ";
        this->insertSourceName(out, sources.front()); 
        break;
    }
    case F_MSB:		
    {
        // position du signe dépendant de la longueur de la source
        const std::string extractIndex(decstr(sources.front().getLength() - 1));
        out += "((_ extract ";
        out += extractIndex;
        out += ' ';
        out += extractIndex;
        out += ") ";

        this->insertSourceName(out, sources.front());  
        break;
    }
    case F_CARRY_ADD:
    {
        // Extension d'1 bit des opérandes afin d'extraire le bit fort de leur somme

        const std::string extractIndex(decstr(sources.front().getLength()));
        const std::string extendSource("((_ zero_extend 1) ");

        out += "((_ extract ";
        out += extractIndex;
        out += ' ';
        out += extractIndex;
        out += ") (bvadd ";

        // zeroextend de l'opérande src/dest
        out += extendSource;
        this->insertSourceName(out, sources.front());
        out += ") ";

        // zeroextend de l'opérande src
        out += extendSource;
        this->insertSourceName(out, sources[1]);
        out += ")) ";

        break;
    }
    case F_CARRY_SUB:
    {
        // bvult renvoie True si opérande 1 < opérande 2
        out += "(ite (bvult ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        out += ") #b1 #b0";
        break;   
    }
    case F_CARRY_SHL:
    {
        // dernier bit ejecté vers la gauche = bit (length - count), count marqué (8 bits)
        // récupération par LSB (src >> (length - count))
        // ATTENTION : count doit etre auparavant masqué à 0x1f ou 0x3f
        out += "((_ extract 0 0) (bvlshr ";
        this->insertSourceName(out, sources.front());

        out += " (bvsub #x";
        out += StringHex(lengthOfResult, 2, false); // length sur 2 digits, pas de prefixe
        
        // masquage du déplacement 0x1f ou 0x3f en 64bits 
        out += " (bvand ";
        this->insertSourceName(out, sources[1]);
        out += (lengthOfResult == 64) ? " #x3f)))" : " #x1f)))";

        break;
    }
    case F_CARRY_SHR:
    {
        // dernier bit ejecté vers la gauche = bit (count - 1), count marqué (8 bits)
        // récupération par LSB (src >> (count - 1))
        // ATTENTION : count doit etre auparavant masqué à 0x1f ou 0x3f
        out += "((_ extract 0 0) (bvlshr ";
        this->insertSourceName(out, sources.front());

        // soustraction apres masquage du déplacement 0x1f ou 0x3f en 64bits 
        out += " (bvsub (bvand ";
        this->insertSourceName(out, sources[1]);
        out += "(_ bv1 ";
        out += decstr(lengthOfResult);
        out += "))))";

        break;
    }
    case F_CARRY_BITBYTE:
    {
        // AND de la source avec (1<<numero bit). Si résultat nul => booléen vaudra 0, sinon 1
        // le numéro du bit est calculé modulo 16/32/64 (soit un AND avec 15/31/63)
        UINT32 srcLength = sources.front().getLength(); // nombre de bits de la source
        const std::string srcLengthName(decstr(srcLength)); // représentation en string

        out += "(ite (= (_ bv0 ";
        out += srcLengthName; // nombre 0 sur x bits
        
        // AND de source0 avec (bvshl (_bv1 'len') (bvand 'numero' (_bv15/31/63 'len')))
        out += ") (bvand ";
        this->insertSourceName(out, sources.front());
        out += " (bvshl (_ bv1 ";
        out += srcLengthName; // nombre 1 sur x bits
        out += ") (bvand ";
        this->insertSourceName(out, sources[1]);

        // nombre 15/31/64 sur 'len' bitsq
        out += " (_ bv";
        out += decstr(srcLength - 1);
        out += ' ';
        out += srcLengthName;
        out += "))))) #b0 #b1";
        break;
    }
    case F_PARITY:	
    {
        // PARITY : parité de l'octet faible de la variable
        // source http://graphics.stanford.edu/~seander/bithacks.html
        // char v;  v ^= v >> 4;   v &= 0xf;   p = (0x6996 >> v) & 1; 
        //   parité de v = parité de p. 
        //   Si p = 1, parité sera 0 => inverser le résultat (d'ou le bvnot)

        out += "(let ((t0 ((_ extract 7 0) "; // seuls les 8 bits faibles sont considérés
        this->insertSourceName(out, sources.front());
        out += "))) " \
            "(let ((t1 (bvlshr t0 #x04))) " \
            "(let ((t2 (bvxor t1 t0))) " \
            "(let ((t3 (bvand t2 #x0f))) " \
            "(let ((t4 (bvlshr #x6996 ((_ zero_extend 8) t3)))) " \
            "(let ((t5 ((_ extract 0 0) t4))) " \
            "(bvnot t5))))))";

        break;
    }
    case F_IS_NULL:	
    case F_CARRY_NEG:
    {
        UINT32 srcLength = sources.front().getLength();
        // comparaison de la source au nombre 0 représenté sur "length" bits
        out += "(ite (= (_ bv0 ";
        out += decstr(srcLength);
        out += ") ";
        this->insertSourceName(out, sources.front());

        // IS_ZERO = si égal à 0 => 1, F_CARRY_NEG l'inverse
        out += (rel == F_IS_NULL) ? " ) #b1 #b0" : " ) #b0 #b1";	
        break;
    }
    case F_ARE_EQUAL:
    {
        out += "(ite (= ";
        this->insertSourceName(out, sources.front());
        out += ' ';
        this->insertSourceName(out, sources[1]);
        out += ") #b1 #b0";
        break;
    }
    case F_OVERFLOW_ADD:	
    case F_OVERFLOW_SUB:	
    {
        // source : http://www.emulators.com/docs/nx11_flags.htm
        // ADD : Formule reprise à partir de BOCHS 2.6
        // OF(A+B) = MSB de (A XOR RESULT) AND (B XOR RESULT)
        // SUB : formule de BOCHS 2.3.5 (BOCHS 2.6 fait différemment)
        // OF(A-B) = MSB de (A XOR RESULT) AND (B XOR A)

        // source 0 = source A (marquée ou non) 
        // source 1 = source B (marquée ou non)   
        // source 2 = résultat (forcément marqué)

        // index d'extraction du MSB
        const std::string extractIndex(decstr(sources.front().getLength() - 1));
       
        out += "((_ extract ";
        out += extractIndex;
        out += ' ';
        out += extractIndex;
        out += ") ";
                
        // A XOR RESULT
        out += "(bvand (bvxor ";
        this->insertSourceName(out, sources.front());  
        out += ' ';
        this->insertSourceName(out, sources[2]);
                
        // B XOR RESULT (si ADD) ou B XOR A (si SUB)
        out += ") (bvxor ";  
        this->insertSourceName(out, sources[1]);
        out += ' ';
        if (rel == F_OVERFLOW_ADD)  this->insertSourceName(out, sources[2]);
        else                        this->insertSourceName(out, sources.front());

        out += "))";	
        break;
    }
    case F_OVERFLOW_INC:	
    case F_OVERFLOW_DEC: // idem OVERFLOW_NEG
    {
        // Le flag est mis à 1 si et seulement si
        // INC : la source vaut 0x7f/0x7fff/0x7fffffff
        // DEC : la source vaut 0x80/0x8000/0x80000000
               
        // ajout des "f" ou des "0" selon la longueur de la source
        // 8 bits : ajout d'un caractère, 16b : ajout de 3 caractères
        // 32b : 7 caractères, 64b : ajout de 15 caractères
        // => formule = ajout de "(srcLength / 4) - 1" caractères
        char c = (rel == F_OVERFLOW_INC) ? 'f' : '0';
        UINT32 nb = (sources.front().getLength() >> 2) - 1;
        const std::string suffix(nb, c);

        out += "(ite (= ";
        this->insertSourceName(out, sources.front());
        out += (rel == F_OVERFLOW_INC) ? " #x7" : " #x8";
        out += suffix;
        out += ") #b1 #b0";	
        break;
    }
    case F_OVERFLOW_SHL:	
    {
        // For 1-left shifts, the OF flag is set to 0 if the most-significant bit of the result 
        // is the same as the CF flag; otherwise, it is set to 1.
        // OF = (MSB "RESULT" == MSB "SOURCE") ? 0 : 1
        
        const std::string indexMSB(decstr(sources.front().getLength() - 1));
        const std::string extractMsb("((_ extract " + indexMSB + ' ' + indexMSB + ") ");

        out += "(ite (= ";
        // 1) extraction msb du resultat
        out += extractMsb;
        this->insertSourceName(out, sources.front());
                
        // 2) extraction msb de la source
        out += ") ";
        extractMsb;
        this->insertSourceName(out, sources[1]);

        out += ")) #b0 #b1";
        break;
    }
    case F_OVERFLOW_ROL: // idem pour OVERFLOW_ROR
    {
        // ite (= (LSB 'src0' MSB 'src0') #b0 #b1)
        const std::string indexMSB = decstr(sources.front().getLength() - 1);
        
        out += "(ite (= ((_ extract 0 0) ";
        this->insertSourceName(out, sources.front());
        out += ") ((_ extract ";
        out += indexMSB;
        out += ' ';
        out += indexMSB;
        out += ") ";
        this->insertSourceName(out, sources.front());
        out +=")) #b0 #b1";
        
        break;
    }
    case F_OVERFLOW_RCL: // idem pour OVERFLOW_RCR
    {
        // ite (= ('src1' MSB 'src0') #b0 #b1)
        const std::string indexMSB = decstr(sources.front().getLength() - 1);
        
        out += "(ite (= ";
        this->insertSourceName(out, sources[1]);
        out += " ((_ extract ";
        out += indexMSB;
        out += ' ';
        out += indexMSB;
        out += ") ";
        this->insertSourceName(out, sources.front());
        out +=")) #b0 #b1";
        
        break;
    }
    case F_CARRY_IMUL:
    case F_CARRY_MUL:
    default: 
        out += "non codé default"; 
        break;
    } // end switch 

    // Parenthèses fermantes puis enregistrement dans la formule
    // en mode debug, ajout de la relation en toutes lettres
    #if DEBUG
    this->m_formula << out << "));" << enum_strings[rel] << '\n';
    #else
    this->m_formula << out << "));" << '\n';
    #endif
}

void SolverFormula::declareConstraintHeader(ADDRINT insAddress, PREDICATE p)
{
    // entete de formule : insertion d'un commentaire
    // avec n° de contrainte, adresse et type de contrainte (si DEBUG)
    this->m_formula << ";\n; contrainte " << std::dec << ++(this->m_iAssert);
    this->m_formula << " (adresse " << hexstr(insAddress);

#if DEBUG
    // on ne prend que les conditions "positives", les négatives
    // étant traitées par inversion du saut pris
    switch (p)
    {
    case PREDICATE_BELOW :          this->m_formula << " - BELOW";          break;
    case PREDICATE_BELOW_OR_EQUAL : this->m_formula << " - BELOW OR EQUAL"; break;
    case PREDICATE_LESS :           this->m_formula << " - LESS";           break;
    case PREDICATE_LESS_OR_EQUAL :  this->m_formula << " - LESS OR EQUAL";  break;
    case PREDICATE_OVERFLOW :       this->m_formula << " - OVERFLOW";       break;
    case PREDICATE_PARITY :         this->m_formula << " - PARITY";         break;
    case PREDICATE_SIGN :           this->m_formula << " - SIGN";           break;
    case PREDICATE_ZERO :           this->m_formula << " - ZERO";           break;
    default:                        this->m_formula << " - INCONNU !!";     break;
    }
#endif

    // fin de ligne
    this->m_formula << ")\n;\n";
}

void SolverFormula::declareConstraintFooter(const std::string &number, bool taken)
{
    this->m_formula << "(assert (= C_" << number << (taken ? " true))\n" : " false))\n");

    // Si le nombre maximal de contraintes est atteint : quitter le pintool via la fonction "Fini"
    // code = 3 (NOMBRE MAXIMAL DE CONTRAINTES)
    // si maxConstraints est nul, ce csa n'arrive jamais (la première contrainte est la n°1)
    if (this->m_iAssert == maxConstraints)  PIN_ExitApplication(3);
}

void SolverFormula::addConstraint_OVERFLOW(TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_OVERFLOW);

    // 2) déclaration de la formule de contrainte  OF = 1  Overflow
    // déclaration du flag marqué, et récursivement de ses sources
    this->declareObject(pTmgrTls->getTaintOverflowFlag());
    
    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber; 
        
    // formule : OF == 1
    constraint += "() Bool (= ";
    constraint += pTmgrTls->getTaintOverflowFlag()->getName();
    constraint += " #b1))\n";

    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_OVERFLOW

void SolverFormula::addConstraint_PARITY(TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_PARITY);

    // 2) déclaration de la formule de contrainte  PF = 1 Parity
    // déclaration du flag marqué, et récursivement de ses sources
    this->declareObject(pTmgrTls->getTaintParityFlag());
    
    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber;  
        
    // formule : PF == 1
    constraint += "() Bool (= ";
    constraint += pTmgrTls->getTaintParityFlag()->getName();
    constraint += " #b1))\n";

    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_PARITY

void SolverFormula::addConstraint_SIGN(TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_SIGN);
    
    // 2) déclaration de la formule de contrainte   SIGN : SF = 1
    // déclaration du flag marqué, et récursivement de ses sources
    this->declareObject(pTmgrTls->getTaintSignFlag());
    
    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber; 
        
    // formule : SF == 1
    constraint += "() Bool (= ";
    constraint += pTmgrTls->getTaintSignFlag()->getName();
    constraint += " #b1))\n";

    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_SIGN

void SolverFormula::addConstraint_ZERO(TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_ZERO);
    
    // 2) déclaration de la formule de contrainte ZF = 1 Equal/zero
    // déclaration du flag marqué, et récursivement de ses sources
    this->declareObject(pTmgrTls->getTaintZeroFlag());
    
    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber;
        
    // formule : ZF == 1
    constraint += "() Bool (= ";
    constraint += pTmgrTls->getTaintZeroFlag()->getName();
    constraint += " #b1))\n";

    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_ZERO

void SolverFormula::addConstraint_BELOW(TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_BELOW);

    // 2) déclaration de la formule de contrainte	CF = 1   Below	
    // déclaration du flag marqué, et récursivement de ses sources
    this->declareObject(pTmgrTls->getTaintCarryFlag());
    
    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber;  
        
    // formule : ZF == 1
    constraint += "() Bool (= ";
    constraint += pTmgrTls->getTaintCarryFlag()->getName();
    constraint += " #b1))\n";
    
    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_BELOW

void SolverFormula::addConstraint_BELOW_OR_EQUAL
    (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken, ADDRINT flagsValue) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_BELOW_OR_EQUAL);
    
    // 2) formule de contrainte  (CF or ZF) = 1  Below or equal	
    // déclaration des flags marqués, et récursivement de leurs sources
    if (pTmgrTls->isCarryFlagTainted()) this->declareObject(pTmgrTls->getTaintCarryFlag());
    if (pTmgrTls->isZeroFlagTainted())  this->declareObject(pTmgrTls->getTaintZeroFlag());

    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber;
        
    // formule : (CF or ZF) == 1
    constraint += "() Bool (= (bvor ";
        
    if (pTmgrTls->isCarryFlagTainted())
    {
        constraint += pTmgrTls->getTaintCarryFlag()->getName();
        constraint += ' ';
    }
    else constraint += ((flagsValue >> CARRY_FLAG) & 1) ? "#b1 " : "#b0 ";

    if (pTmgrTls->isZeroFlagTainted()) constraint += pTmgrTls->getTaintZeroFlag()->getName();
    else constraint += ((flagsValue >> ZERO_FLAG) & 1) ? "#b1" : "#b0";

    constraint += ") #b1))\n";
 
    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_BELOW_OR_EQUAL

void SolverFormula::addConstraint_LESS
    (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken, ADDRINT flagsValue) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_LESS);
    
    // 2) déclaration de la formule de contrainte  (SF xor OF) = 1 Less
    // déclaration des flags marqués, et récursivement de leurs sources
    if (pTmgrTls->isSignFlagTainted())     this->declareObject(pTmgrTls->getTaintSignFlag());
    if (pTmgrTls->isOverflowFlagTainted()) this->declareObject(pTmgrTls->getTaintOverflowFlag());

    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber;
        
    // formule : (SF Xor OF) == 1
    constraint += "() Bool (= (bvxor ";
    
    if (pTmgrTls->isSignFlagTainted())
    {
        constraint += pTmgrTls->getTaintSignFlag()->getName();
        constraint += ' ';
    }
    else constraint += ((flagsValue >> SIGN_FLAG) & 1) ? "#b1 " : "#b0 ";
        
    if (pTmgrTls->isOverflowFlagTainted()) constraint += pTmgrTls->getTaintOverflowFlag()->getName();
    else constraint += ((flagsValue >> OVERFLOW_FLAG) & 1) ? "#b1" : "#b0";

    constraint += ") #b1))\n";

    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_LESS

void SolverFormula::addConstraint_LESS_OR_EQUAL
    (TaintManager_Thread *pTmgrTls, ADDRINT insAddress, bool isTaken, ADDRINT flagsValue) 
{
    // 1) définition de l'entête de la contrainte
    this->declareConstraintHeader(insAddress, PREDICATE_LESS_OR_EQUAL);
    
    // 2) déclaration de la formule de contrainte (SF xor OF) or ZF) = 1 		
    // déclaration des flags marqués, et récursivement de leurs sources
    if (pTmgrTls->isSignFlagTainted())     this->declareObject(pTmgrTls->getTaintSignFlag());
    if (pTmgrTls->isOverflowFlagTainted())	this->declareObject(pTmgrTls->getTaintOverflowFlag());
    if (pTmgrTls->isZeroFlagTainted())	    this->declareObject(pTmgrTls->getTaintZeroFlag());

    // declaration de la contrainte : declaration de l'objet
    const std::string constraintNumber(decstr(this->m_iAssert));
    std::string constraint("(define-fun C_");
    constraint += constraintNumber;
        
    // formule : ((SF xor OF) or ZF) == 1
    constraint += "() Bool (= (bvor (bvxor ";

    if (pTmgrTls->isSignFlagTainted())
    {
        constraint += pTmgrTls->getTaintSignFlag()->getName();
        constraint += ' ';
    }
    else constraint += ((flagsValue >> SIGN_FLAG) & 1) ? "#b1 " : "#b0 ";
        
    if (pTmgrTls->isOverflowFlagTainted())	
    {
        constraint += pTmgrTls->getTaintOverflowFlag()->getName();
        constraint += ") ";
    }
    else constraint += ((flagsValue >> OVERFLOW_FLAG) & 1) ? "#b1) " : "#b0)";

    if (pTmgrTls->isZeroFlagTainted()) constraint += pTmgrTls->getTaintZeroFlag()->getName();
    else constraint += ((flagsValue >> ZERO_FLAG) & 1) ? "#b1" : "#b0";

    constraint += ") #b1))\n";
    
    this->m_formula << constraint;

    // 3) déclaration de l'assertion en fin de contrainte
    // selon que la branche a été prise ou non
    this->declareConstraintFooter(constraintNumber, isTaken);
} // addConstraint_LESS_OR_EQUAL

// envoi des denières données : nombre total de contraintes
void SolverFormula::final() 
{
    WINDOWS::DWORD cbWritten = 0;
    
    // insertion du nombre total de contraintes 
    this->m_formula << "@" << std::dec << this->m_iAssert;
    
    // envoi de la formule en entier dans le pipe   (= stdout en mode debug)
    WINDOWS::WriteFile(hPipe, 
        this->m_formula.str().c_str(), 
        static_cast<WINDOWS::DWORD>(this->m_formula.str().size()), // pour eviter C4267 en x64 
        &cbWritten, 
        NULL);
    WINDOWS::FlushFileBuffers(hPipe);
}
