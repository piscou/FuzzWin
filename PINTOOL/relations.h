// type de relation entre TaintObjects
enum Relation 
{
    /******************************************************/
    /**** Relations de construction des objets marqués ****/
    /******************************************************/
    
    //! BYTESOURCE : TaintObject issu de la source suivie
    //! Source1 : offset dans l'entrée (variable 32bits)
    BYTESOURCE = 0, 
    //! EXTRACT : Source 1 = source, Source 2 = index d'extraction (valeur 8bits)
    EXTRACT,
    //! CONCAT : concaténation des sources (longueurs différentes acceptées)
    // 1ere source = poids faible, dernière source : poids fort
    CONCAT,

    /********************************************************/
    /**** Relations de modélisation des instructions x86 ****/
    /********************************************************/
    
    /** DATAXFER **/
    //! ASSIGN : Source 1 = source, même longueur que destination
    X_ASSIGN, 
    //! SIGN_EXTEND : Source 1 = source (longueur < à destination)
    X_SIGNEXTEND,
    
    /**  BINARY **/
    //! ADD : source 1 = source, source 2 = src/dest
    X_ADD,
    //! INC : source 1 = source
    X_INC,
    //! SUB : source 1 = source, source 2 = src/dest
    X_SUB, 
    //! DEC : source 1 = source
    X_DEC,
    //! NEG : source 1 = source
    X_NEG,
    //! X_MUL : voir X_IMUL
    X_MUL, 
    //! X_IMUL : source 1 = source, source 2 = src/dest.
    X_IMUL,
    // division non signée avec quotient et reste 
    X_DIV_QUO, 
    X_DIV_REM, 
    // division signée avec quotient et reste
    X_IDIV_QUO, 
    X_IDIV_REM,

    /** LOGICAL **/
    //! AND : source 1 = source, source 2 = src/dest 
    X_AND, 
    //! OR : source 1 = source, source 2 = src/dest
    X_OR, 
    //! XOR : source 1 = source, source 2 = src/dest
    X_XOR, 
    //! NOT : source 1 = src/dest
    X_NOT,

    /** SHIFT **/
    //! SHL : source 1 = emplacement déplacé, source 2 = déplacement (8bits, valeur ou objet)
    // si déplacement non marqué, il est déjà masqué à 0x1f ou 0x3f
    // si déplacement marqué, le marquage sera fait dans la formule
    X_SHL, 
    //! SHR : source 1 = emplacement déplacé, source 2 = déplacement (8bits, valeur ou objet)
    // si déplacement non marqué, il est déjà masqué à 0x1f ou 0x3f
    // si déplacement marqué, le marquage sera fait dans la formule
    X_SHR, 
    //! SAR : source 1 = emplacement déplacé, source 2 = déplacement (8bits, valeur ou objet)
    // si déplacement non marqué, il est déjà masqué à 0x1f ou 0x3f
    // si déplacement marqué, le marquage sera fait dans la formule
    X_SAR,

    /** ROTATE **/
    //! ROR : source 1 = emplacement déplacé, source 2 = déplacement (8bits, valeur ou objet)
    X_ROR,
    //! ROL : source 1 = emplacement déplacé, source 2 = déplacement (8bits, valeur ou objet)
    X_ROL, 
    //! RCR : source 1 = emplacement déplacé, source 2 = CF (1 bit) marqué ou valeur,
    // source 3 = déplacement (8bits, valeur ou objet)
    X_RCR, 
    //! RCL : source 1 = emplacement déplacé, source 2 = CF (1 bit) marqué ou valeur,
    // source 3 = déplacement (8bits, valeur ou objet)
    X_RCL,

    /** BITBYTE **/
    // COMPLEMENT_BIT : inverse le bit concerné dans la source (eq. BTC)
    // src0 : src, src1 : numéro du bit (obj marqué de longueur = à la source)
    // src1 est sur 16/32/64bits, 8 bits impossible. position bit marqué sinon ce serait un EXTRACT
    X_COMPLEMENT_BIT,
    // SET_BIT : met à 1 le bit concerné dans la source (eq. BTS)
    // src0 : src, src1 : numéro du bit (obj marqué de longueur = à la source)
    // src1 est sur 16/32/64bits, 8 bits impossible. position bit marqué sinon ce serait un EXTRACT
    X_SET_BIT,
    // CLEAR_BIT : met à 0 le bit concerné dans la source (eq. BTR)
    // src0 : src, src1 : numéro du bit (obj marqué de longueur = à la source)
    // src1 est sur 16/32/64bits, 8 bits impossible. position bit marqué sinon ce serait un EXTRACT
    X_CLEAR_BIT,

    /*******************************************************************/
    /**** Relations de modelisation des effets de bords (flags) x86 ****/
    /*******************************************************************/
    
    // LSB : bit de poids faible. source 0 = source
    F_LSB,
    // MSB : bit de poids fort. source 0 = source. Equivaut au Sign Flag 
    F_MSB,

    /* CARRY_FLAG */
    // CARRY_ADD : Source0 : src/dest, source1 : src
    F_CARRY_ADD,
    // CARRY_SUB : Source0 : src/dest, source1 : src
    F_CARRY_SUB,
    // CARRY_NEG : Source0 : src (vrai ssi source non nulle)
    F_CARRY_NEG,
    // CARRY_MUL : Source0 : resultat. Si partie haute du resultat nulle, CF mis à 1
    F_CARRY_MUL, 
    // CARRY_IMUL : Source0 : resultat; si resultat = sign_extend partie basse, alors CF mis à 1
    F_CARRY_IMUL,  
    // CARRY_SHL : denier bit ejecté (cas ou la source est marqué sinon traitement direct par extract)
    // Source0 : source, source1 : depl (marqué - 8bits, sera masqué à 0x1f ou 0x3f dans la formule)
    F_CARRY_SHL,
    // CARRY_SHR : denier bit ejecté (cas ou la source est marqué sinon traitement direct par extract)
    // Source0 : source, source1 : depl (marqué - 8bits, sera masqué à 0x1f ou 0x3f dans la formule)
    F_CARRY_SHR,
    // CARRY_SAR : denier bit ejecté (cas ou la source est marqué sinon traitement direct par extract)
    // Source0 : source, source1 : depl (marqué - 8bits, sera masqué à 0x1f ou 0x3f dans la formule)
    // IDENTIQUE A CARRY_SHR car le deplacement est masqué 
    F_CARRY_SAR = F_CARRY_SHR,
   
    // CARRY_RCL : denier bit ejecté (cas ou la source est marqué sinon traitement direct par extract)
    // Source0 : source, source1: depl (marqué - 8bits, sera masqué à 0x1f ou 0x3f dans la formule)
    F_CARRY_RCL,
    // CARRY_RCR : denier bit ejecté (cas ou la source est marqué sinon traitement direct par extract)
    // Source0 : source, source1: depl (marqué - 8bits, sera masqué à 0x1f ou 0x3f dans la formule)
    F_CARRY_RCR, 
    // CARRY_BITBYTE : extraction du bit 'b' de la source, lorsque la position
    // du bit est marqué. !! source0 et source1 sont de la meme taille
    // Source0 : source, source1 : n° bit (marqué). Sera ajusté modulo 16/32/64
    F_CARRY_BITBYTE,

    /** PARITY_FLAG **/
    // PARITY. source 0 = resultat. seuls les 8 bits faibles seront considérés
    F_PARITY,

    /** ZERO_FLAG **/
    // F_IS_NULL : 1 si source0 est nulle, 0 sinon
    F_IS_NULL,
    // F_ARE_EQUAL : 1 si source0 et source1 sont égales, 0 sinon
    F_ARE_EQUAL,

    /** OVERFLOW_FLAG **/
    // OF_ADD : Src0 : src/dest, src1 : src, src2 : result
    F_OVERFLOW_ADD,
    // OF_SUB : Src0 : src/dest, src1 : src, src2 : result
    F_OVERFLOW_SUB, 
    // OF_INC : Src0 : src/dest
    F_OVERFLOW_INC,
    // OF_DEC : Src0 : src/dest
    F_OVERFLOW_DEC,
    F_OVERFLOW_NEG = F_OVERFLOW_DEC, // formule identique NEG et DEC
    
    // OF_SHL (ssi depl == 1). 1 si signe change entre src et resultat. 
    // Src0 = resultat, src1 = src
    F_OVERFLOW_SHL, 
    // OF_SHRD (ssi depl == 1). 1 si signe avant et apres change 
    // donc si MSB src != LSB Bit Pattern. .
    // Source0 = concatenation bitPattern(partie haute) et source shiftée
    F_OVERFLOW_SHRD,
    // OF_ROL (ssi depl == 1). 1 si signe change entre src et resultat.
    // Pour ROL <=> LSB(result) = MSB(result). Source0 = result
    F_OVERFLOW_ROL,
    // OF_ROR (ssi depl == 1). 1 si signe change entre src et resultat.
    // Pour ROR <=> LSB(src) = MSB(src). Source0 = src, et donc identique à ROL
    F_OVERFLOW_ROR = F_OVERFLOW_ROL,
    // OF_RCL (ssi depl == 1): 0 si valeur CF AVANT rotation == MSB result
    // Src0 = result, src1 : CF_after (1bit)
    F_OVERFLOW_RCL,
    // OF_RCR (ssi depl == 1): 0 si valeur CF AVANT rotation == MSB source
    // Src0 = source, src1 : CF_before (1bit), donc identique RCL
    F_OVERFLOW_RCR = F_OVERFLOW_RCL,

    // AUXILIARY FLAG
    F_AUXILIARY_ADD,
    F_AUXILIARY_NEG,
    F_AUXILIARY_SUB,
    F_AUXILIARY_CMP,
    F_AUXILIARY_INC,
    F_AUXILIARY_DEC,

    RELATION_LAST
};

#if DEBUG
const static std::string enum_strings[RELATION_LAST] = 
{
    // TaintObject issu de la source suivie
    "BYTESOURCE", 

    // construction d'objets par extraction 
    // ou concaténation d'autres objets
    "EXTRACT",
    "CONCAT",

    /**** Relations de modelisation des instructions x86 ****/

    // DATAXFER
    "X_ASSIGN", "X_SIGNEXTEND",
    
    // BINARY
    "X_ADD", "X_INC", "X_SUB", "X_DEC", "X_NEG",
    "X_MUL", "X_IMUL",
    // division non signée avec quotient et reste
    "X_DIV_QUO", "X_DIV_REM", 
    // division signée avec quotient et reste
    "X_IDIV_QUO", "X_IDIV_REM",

    // LOGICAL
    "X_AND", "X_OR", "X_XOR", "X_NOT",

    // SHIFT
    "X_SHL", "X_SHR", "X_SAR",

    // ROTATE
    "X_ROR", "X_ROL", "X_RCR", "X_RCL",

    // BIT_BYTE
    "X_COMPLEMENT_BIT", "X_SET_BIT", "X_CLEAR_BIT",

    /**** Relations de modelisation des effets de bords (flags) x86 ****/
    
    "F_LSB", "F_MSB",   
    
    // CARRY_FLAG
    "F_CARRY_ADD", "F_CARRY_SUB", "F_CARRY_NEG", "F_CARRY_MUL", "F_IMUL",
    "F_CARRY_SHL", "F_CARRY_SHR/SAR",
    "F_CARRY_RCL", "F_CARRY_RCR",
    "F_CARRY_BITBYTE",

    // PARITY FLAG
    "F_PARITY",

    // ZERO FLAG
    "F_IS_NULL",
    "F_ARE_EQUAL",

    // OVERFLOW FLAG
    "F_OVERFLOW_ADD", "F_OVERFLOW_SUB",
    "F_OVERFLOW_INC", "F_OVERFLOW_DEC/NEG",
    "F_OVERFLOW_SHL", "F_OVERFLOW_SHRD",
    "F_OVERFLOW_ROL/RCL", 
    "F_OVERFLOW_RCR/RCL",
    
    // AUXILIARY FLAG
    "F_AUXILIARY_ADD",
    "F_AUXILIARY_NEG",
    "F_AUXILIARY_SUB",
    "F_AUXILIARY_CMP",
    "F_AUXILIARY_INC",
    "F_AUXILIARY_DEC"
};
#endif