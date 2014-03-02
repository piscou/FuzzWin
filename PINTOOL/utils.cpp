#include "utils.h"

void UTILS::cUNHANDLED(INS &ins) 
{ 
    // si l'instruction écrit en mémoire : démarquage de la mémoire
    if (INS_IsMemoryWrite(ins)) 
    {   
        // contrairement à ce qui est fait pour les instructions
        // il n'est pas possible d'utiliser des templates
        // car la taille d'écriture peut etre > à 8 octets (cas SSE et AVX...)
        // on passe donc la taille en parametre, et la fonction appellera
        // UnTaintMemory<8> dans une boucle avec la taille pour compteur
        
        INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) uMEM,
            IARG_FAST_ANALYSIS_CALL,  
            IARG_MEMORYWRITE_EA,  
            IARG_MEMORYWRITE_SIZE,
            IARG_END);
    } 
    
    // récupération de tous les registres de destination, y compris Eflags, et démarquage
    REG reg = INS_RegW(ins, 0); // premier registre accédé en écriture (REG_INVALID si aucun)
    UINT32 kthReg = 0;          // kième registre accédé en écriture

    while ( reg != REG_INVALID() ) // parcours de tous les registres accédés en écriture
    {
        // procédure spécifique pour les flags
        if (reg == REG_GFLAGS) // GFLAGS = (E/R)FLAGS selon l'architecture
        {
            INS_InsertCall (ins, IPOINT_BEFORE, (AFUNPTR) uFLAGS,
                IARG_FAST_ANALYSIS_CALL,
                IARG_THREAD_ID, 
                IARG_END);
        }
        else
        {
            UINT32 regSize = getRegSize(reg); 
            // si registre suivi en marquage, le démarquer
            // impossible de le mettre dans le switch avec un 'continue'
            // car il faut que la ligne 'INS_RegW(ins, ++kthReg)' soit exécutée
            if (regSize) 
            {     
                void (*callbackReg)() = nullptr; // pointeur sur la fonction à appeler
                switch (regSize)        
                {
                    case 1: callbackReg = (AFUNPTR) uREG<8>;  break;
                    case 2: callbackReg = (AFUNPTR) uREG<16>; break;
                    case 4: callbackReg = (AFUNPTR) uREG<32>; break;
                    case 8: callbackReg = (AFUNPTR) uREG<64>; break;
                }
                INS_InsertCall (ins, IPOINT_BEFORE, callbackReg,
                    IARG_FAST_ANALYSIS_CALL, 
                    IARG_THREAD_ID, 
                    IARG_UINT32, reg, 
                    IARG_END);                   
            }
        }
        // récupération du prochain registre sur la liste avant rebouclage
        reg = INS_RegW(ins, ++kthReg);
    } 
} // cUNHANDLED

// démarquage rapide mémoire par callback. Pas de template car taille indéfinie 
void PIN_FAST_ANALYSIS_CALL UTILS::uMEM(ADDRINT address, UINT32 sizeInBytes)
{  
    ADDRINT lastAddress = address + sizeInBytes;
    while (address++ < lastAddress)    pTmgrGlobal->unTaintMemory<8>(address);
}

void PIN_FAST_ANALYSIS_CALL UTILS::uFLAGS(THREADID tid)  
{  
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    pTmgrTls->unTaintAllFlags(); 
}


/************************/
/** ADRESSAGE INDIRECT **/
/************************/

// renvoie le type d'adressage indirect utilisé par l'instruction
void UTILS::cGetKindOfEA(const INS &ins)
{
    REG baseReg     = INS_MemoryBaseReg(ins);      // Registre de base (ou REG_INVALID)
    REG indexReg    = INS_MemoryIndexReg(ins);     // Registre d'index (ou REG_INVALID)
    ADDRDELTA displ = INS_MemoryDisplacement(ins); // déplacement (signé)
    UINT32 scale    = INS_MemoryScale(ins);        // scale (multiplie le registre d'index)
    
    bool hasBaseReg  = (baseReg  != REG_INVALID()); 
    bool hasIndexReg = (indexReg != REG_INVALID()); 
    bool hasDispl    = (displ    != 0);          
    UINT32 hasScale  = (scale    != 1);         

    // construction d'un masque : cela évite les multiples IF...ELSE
    // ici un seul switch/case suffira pour définir le type d'EA
    // BASE : INDEX : SCALE : DISPL
    UINT32 mask = (hasBaseReg << 3) + (hasIndexReg << 2) + (hasScale << 1) + hasDispl; 
    
    // variables pour l'insertion de la fonction d'analyse : arguments et pointeur de fonction
    IARGLIST args = IARGLIST_Alloc();
    void (*callback)();

    switch (mask)
    {
    case 15:  _MAKE_ARGS_EA(BISD);  break; // 0b1111 => |BISD|
    case 14:  _MAKE_ARGS_EA(BIS);   break; // 0b1110 => |BIS |
    case 13:  _MAKE_ARGS_EA(BID);   break; // 0b1101 => |BI D|
    case 12:  _MAKE_ARGS_EA(BI);    break; // 0b1100 => |BI  |
    case 9:   _MAKE_ARGS_EA(BD);    break; // 0b1001 => |B  D|
    case 8:   _MAKE_ARGS_EA(B);     break; // 0b1000 => |B   |
    case 7:   _MAKE_ARGS_EA(ISD);   break; // 0b0111 => | ISD|
    case 6:   _MAKE_ARGS_EA(IS);    break; // 0b0110 => | IS |        
    default:  return;  // autres cas : pas de marquage possible
    }

    INS_InsertCall(ins, IPOINT_BEFORE, callback, 
        IARG_CALL_ORDER, CALL_ORDER_FIRST, // cela sera tjs le premier callback pour l'instruction
        IARG_IARGLIST, args,               // liste des arguments
        IARG_END);
    IARGLIST_Free(args);  
} // getKindOfEA


/*****************************************************************************/
/** UTILITAIRE DE CREATION DE L'OBJET CORRESPONDANT A UN ADRESSAGE INDIRECT **/
/*****************************************************************************/

// elles font partie des fonctions d'analyse 
// lorsque l'instruction accède à la mémoire, en lecture ou écriture

// Chaque fonction va vérifier si la valeur de l'adresse calculée est marquée
// (NB : on teste la valeur de l'adresse, pas la valeur pointée par l'adresse !!)

// s'il y a marquage, un objet symbolique représentant le calcul de l'adresse
// est créé, et stocké dans TaintManager ('storeTaintEffectiveAddress')

// dans les fonctions d'analyse ayant pour source ou destination la mémoire
// la fonction testera le marquage dans taintManager ('isEffectiveAddressTainted')
// si marqué, un objet de type "LOAD" ou "STORE" sera créé avec pour sources 
// 1) le marquage de la mémoire (ce peut etre une valeur ou un objet marqué)
// 2) l'adresse réelle de la mémoire accédee (ObjectSource valeur sur 32 ou 64 bits)
// 3) l'objet qui permet de calculer cette addresse
// 4) EFFACEMENT DE L'OBJET APRES RECUPERATION, pour laisser un objet vide pour le prochain appel

// lors de la construction de la formule, lors de la rencontre d'un objet "LOAD" ou "STORE"
// une contrainte sera ajoutée du type 'adresse réelle = objet'
// cette contrainte, lorsqu'elle sera inversée, permettra de trouver une autre valeur pour l'adresse

/***** MODE 32BITS ******/
#if TARGET_IA32

void UTILS::computeEA_BISD(FUNCARGS_BISD)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale+displ)
//  SI BASE MARQUEE  source1 = marquage base
//  SINON            source1 = valeur registre de base
//
//  SI INDEX MARQUE  IS = index*scale (via SHL); source2 = IS +/- displ (via ADD ou SUB)
//  SINON            source2 = valeur (index*scale +/- displ)
//
//  EA = ADD(source1, source2)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<32>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<32>(baseReg);

    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BISD");
        
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintDword tdwEAValue(X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue))
                               : ObjectSource(32, baseRegValue));  
    
        // ajout d'index*scale +/- displ (SOURCE 2), selon son marquage 
        // BISD : LE SCALE EST DIFFERENT DE 1, DISPL NON NUL
        if (isIndexRegTainted) 
        {      
            // valeur du déplacement (avec scale = 2^depl)
            UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
            // 1) opération index*scale traité comme un SHL car déplacement multiple de 2 
            // source 1 : le registre d'index (forcément marqué)
            // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
            TaintDwordPtr tdwISptr = std::make_shared<TaintDword>
                (X_SHL, 
                ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)),
                ObjectSource(8, shiftValue)
                );  
            
            // 2) opération IS +/- displ 
            Relation rel    = (displ > 0) ? X_ADD : X_SUB;
            UINT32 absDispl = abs(displ);
            TaintDword tdwISD(rel, ObjectSource(tdwISptr), ObjectSource(32, absDispl));

            tdwEAValue.addSource(std::make_shared<TaintDword>(tdwISD)); 
        }
        // ajout de la valeur numérique
        else tdwEAValue.addConstantAsASource<32>(indexRegValue*scale + displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(tdwEAValue));
    }
} // computeEA_BISD(32bits)

void UTILS::computeEA_BIS(FUNCARGS_BIS)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale)
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
//
//  SI INDEX MARQUE source2 = index*scale (via SHL)
//  SINON           source2 = valeur (index*scale)
//  EA = ADD(source1, source2)

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<32>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<32>(baseReg);

    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BIS");
        
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintDword tdwEAValue(X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue))
                               : ObjectSource(32, baseRegValue));  
    
        // ajout d'index*scale +/- displ (SOURCE 2), selon son marquage 
        // BIS : LE SCALE EST DIFFERENT DE 1
        if (isIndexRegTainted) 
        {      
            // valeur du déplacement (avec scale = 2^depl)
            UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
            // 1) opération index*scale traité comme un SHL car déplacement multiple de 2 
            // source 1 : le registre d'index (forcément marqué)
            // source 2 : shiftValue (sur 8 bits, comme tous les shifts
            tdwEAValue.addSource(std::make_shared<TaintDword>(X_SHL, 
                ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)),
                ObjectSource(8, shiftValue)
                )); 
        }
        // ajout de la valeur numérique
        else tdwEAValue.addConstantAsASource<32>(indexRegValue*scale);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(tdwEAValue));
    }
} // computeEA_BIS(32bits)

void UTILS::computeEA_BID(FUNCARGS_BID)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale+displ)
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
//
//  SI INDEX MARQUE source2 = index marqué +/- displ 
//  SINON           source2 = valeur (index +/- displ)
//
// EA = ADD(source1, source2)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<32>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<32>(baseReg);
    
    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BID");
    
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintDword tdwEAValue(X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue))
                               : ObjectSource(32, baseRegValue));  
    
        // ajout d'index +/- displ (SOURCE 2), selon son marquage 
        // BID : SCALE = 1, DISPL NON NUL
        if (isIndexRegTainted) 
        {      
            Relation rel    = (displ > 0) ? X_ADD : X_SUB;
            UINT32 absDispl = abs(displ);

            tdwEAValue.addSource(std::make_shared<TaintDword>(rel, 
                ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)), 
                ObjectSource(32, absDispl))); 
        }
        // ajout de la valeur numérique
        else tdwEAValue.addConstantAsASource<32>(indexRegValue + displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(tdwEAValue));
    }
} // computeEA_BID(32bits)

void UTILS::computeEA_BI(FUNCARGS_BI)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale+displ)
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
//
//  SI INDEX MARQUE source2 = index marqué
//  SINON           source2 = valeur index
//
// EA = ADD(source1, source2)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<32>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<32>(baseReg);

    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BI");
        // source 1 : base
        ObjectSource baseSrc((isBaseRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue))
            : ObjectSource(32, baseRegValue));
        
        // source 2 : index
        ObjectSource indexSrc((isIndexRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue))
            : ObjectSource(32, indexRegValue));

        // ajout des deux sources et stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(X_ADD, baseSrc, indexSrc));
    }
    
} // computeEA_BI(32bits)

void UTILS::computeEA_BD(FUNCARGS_BD)
{
// pour construire l'EA, on additionne deux entités : la base et le displ
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
// EA = ADD/SUB (selon signe) (source1, displ)
 
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // traitement ssi base marquée
    if (pTmgrTls->isRegisterTainted<32>(baseReg)) 
    {
        _LOGTAINT("BD")
        Relation rel    = (displ > 0) ? X_ADD : X_SUB;
        UINT32 absDispl = abs(displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(rel, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue)), 
            ObjectSource(32, absDispl)));
    }
} // computeEA_BD(32bits)

void UTILS::computeEA_B(FUNCARGS_B)
{
// EA = marquage base
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
 
    // traitement ssi base marquée
    if (pTmgrTls->isRegisterTainted<32>(baseReg)) 
    {
        _LOGTAINT("B")
        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(pTmgrTls->getRegisterTaint<32>(baseReg, baseRegValue));
    }
} // computeEA_B(32bits)

void UTILS::computeEA_ISD(FUNCARGS_ISD)
{
// pour construire l'EA, on additionne deux entités : index*scale et displ
//  SI INDEX MARQUE  IS = index*scale (via SHL); 
//  EA = ADD ou SUB(IS, displ)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
   
    // traitement ssi index marqué, sinon ne rien faire
    if (pTmgrTls->isRegisterTainted<32>(indexReg)) 
    {
        _LOGTAINT("ISD");
   
        // valeur du déplacement (avec scale = 2^depl)
        UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
        // 1) opération index*scale traité comme un SHL car déplacement multiple de 2 
        // source 1 : le registre d'index (forcément marqué)
        // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
        TaintDwordPtr tdwISptr = std::make_shared<TaintDword>
            (X_SHL, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)),
            ObjectSource(8, shiftValue)
            );  
            
        // 2) opération IS +/- displ et stockage dans TaintManager
        Relation rel    = (displ > 0) ? X_ADD : X_SUB;
        UINT32 absDispl = abs(displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(rel, 
            ObjectSource(tdwISptr), 
            ObjectSource(32, absDispl)));
    }
} // computeEA_ISD(32bits)

void UTILS::computeEA_IS(FUNCARGS_IS)
{
    // SI INDEX MARQUE  EA = index*scale (via SHL)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
   
    // traitement ssi index marqué, sinon ne rien faire
    if (pTmgrTls->isRegisterTainted<32>(indexReg)) 
    {
        _LOGTAINT("IS");
   
        // valeur du déplacement (avec scale = 2^depl)
        UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
        // opération index*scale traité comme un SHL car déplacement multiple de 2 
        // source 1 : le registre d'index (forcément marqué)
        // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintDword>(
            X_SHL, 
            ObjectSource(pTmgrTls->getRegisterTaint<32>(indexReg, indexRegValue)),
            ObjectSource(8, shiftValue))); 
    }
} // computeEA_IS(32bits)

#else

void UTILS::computeEA_BISD(FUNCARGS_BISD)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale+displ)
//  SI BASE MARQUEE  source1 = marquage base
//  SINON            source1 = valeur registre de base
//
//  SI INDEX MARQUE  IS = index*scale (via SHL); source2 = IS +/- displ (via ADD ou SUB)
//  SINON            source2 = valeur (index*scale +/- displ)
//
//  EA = ADD(source1, source2)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);

    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<64>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<64>(baseReg);

    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BISD");
        
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintQword tqwEAValue(X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue))
                               : ObjectSource(64, baseRegValue));  
    
        // ajout d'index*scale +/- displ (SOURCE 2), selon son marquage 
        // BISD : LE SCALE EST DIFFERENT DE 1, DISPL NON NUL
        if (isIndexRegTainted) 
        {      
            // valeur du déplacement (avec scale = 2^depl)
            UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
            // 1) opération index*scale traité comme un SHL car déplacement multiple de 2 
            // source 1 : le registre d'index (forcément marqué)
            // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
            TaintQwordPtr tqwISptr = std::make_shared<TaintQword>
                (X_SHL, 
                ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)),
                ObjectSource(8, shiftValue)
                );  
            
            // 2) opération IS +/- displ 
            Relation rel    = (displ > 0) ? X_ADD : X_SUB;
            UINT32 absDispl = abs(displ);
            TaintQword tqwISD(rel, ObjectSource(tqwISptr), ObjectSource(64, absDispl));

            tqwEAValue.addSource(std::make_shared<TaintQword>(tqwISD)); 
        }
        // ajout de la valeur numérique
        else tqwEAValue.addConstantAsASource<64>(indexRegValue*scale + displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(tqwEAValue));
    }
} // computeEA_BISD(64bits)

void UTILS::computeEA_BIS(FUNCARGS_BIS)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale)
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
//
//  SI INDEX MARQUE source2 = index*scale (via SHL)
//  SINON           source2 = valeur (index*scale)
//  EA = ADD(source1, source2)

    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<64>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<64>(baseReg);

    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BIS");
        
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintQword tqwEAValue(X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue))
                               : ObjectSource(64, baseRegValue));  
    
        // ajout d'index*scale +/- displ (SOURCE 2), selon son marquage 
        // BIS : LE SCALE EST DIFFERENT DE 1
        if (isIndexRegTainted) 
        {      
            // valeur du déplacement (avec scale = 2^depl)
            UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
            // 1) opération index*scale traité comme un SHL car déplacement multiple de 2 
            // source 1 : le registre d'index (forcément marqué)
            // source 2 : shiftValue (sur 8 bits, comme tous les shifts
            tqwEAValue.addSource(std::make_shared<TaintQword>(X_SHL, 
                ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)),
                ObjectSource(8, shiftValue)
                )); 
        }
        // ajout de la valeur numérique
        else tqwEAValue.addConstantAsASource<64>(indexRegValue*scale);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(tqwEAValue));
    }
} // computeEA_BIS(64bits)

void UTILS::computeEA_BID(FUNCARGS_BID)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale+displ)
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
//
//  SI INDEX MARQUE source2 = index marqué +/- displ 
//  SINON           source2 = valeur (index +/- displ)
//
// EA = ADD(source1, source2)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<64>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<64>(baseReg);
    
    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BID");
    
        // construction du squelette de l'objet (il y aura au moins une addition)
        // ajout de la base (SOURCE 1) lors de la construction, selon son marquage
        TaintQword tqwEAValue(X_ADD, 
            (isBaseRegTainted) ? ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue))
                               : ObjectSource(64, baseRegValue));  
    
        // ajout d'index +/- displ (SOURCE 2), selon son marquage 
        // BID : SCALE = 1, DISPL NON NUL
        if (isIndexRegTainted) 
        {      
            Relation rel    = (displ > 0) ? X_ADD : X_SUB;
            UINT32 absDispl = abs(displ);

            tqwEAValue.addSource(std::make_shared<TaintQword>(rel, 
                ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)), 
                ObjectSource(64, absDispl))); 
        }
        // ajout de la valeur numérique
        else tqwEAValue.addConstantAsASource<64>(indexRegValue + displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(tqwEAValue));
    }
} // computeEA_BID(64bits)

void UTILS::computeEA_BI(FUNCARGS_BI)
{
// pour construire l'EA, on additionne deux entités : la base, et (index*scale+displ)
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
//
//  SI INDEX MARQUE source2 = index marqué
//  SINON           source2 = valeur index
//
// EA = ADD(source1, source2)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    bool isIndexRegTainted = pTmgrTls->isRegisterTainted<64>(indexReg);
    bool isBaseRegTainted =  pTmgrTls->isRegisterTainted<64>(baseReg);

    // il faut au moins un des registres base ou index marqués, sinon ne rien faire
    if (isIndexRegTainted || isBaseRegTainted) 
    {
        _LOGTAINT("BI");
        // source 1 : base
        ObjectSource baseSrc((isBaseRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue))
            : ObjectSource(64, baseRegValue));
        
        // source 2 : index
        ObjectSource indexSrc((isIndexRegTainted) 
            ? ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue))
            : ObjectSource(64, indexRegValue));

        // ajout des deux sources et stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(X_ADD, baseSrc, indexSrc));
    }
    
} // computeEA_BI(64bits)

void UTILS::computeEA_BD(FUNCARGS_BD)
{
// pour construire l'EA, on additionne deux entités : la base et le displ
//  SI BASE MARQUEE source1 = marquage base
//  SINON           source1 = valeur registre de base
// EA = ADD/SUB (selon signe) (source1, displ)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
 
    // ATTENTION : en 64BITS, possibilité d'adressage RIP-RELATIVE, non suivi en marquage
    // DONC NE PAS INSTRUMENTER SI C'EST LE CAS
    // traitement ssi base marquée
    if (pTmgrTls->isRegisterTainted<64>(baseReg) && (baseReg != REG_RIP)) 
    {
        _LOGTAINT("BD");
        Relation rel    = (displ > 0) ? X_ADD : X_SUB;
        UINT32 absDispl = abs(displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(rel, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue)), 
            ObjectSource(64, absDispl)));
    }
} // computeEA_BD(64bits)

void UTILS::computeEA_B(FUNCARGS_B)
{
// EA = marquage base
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    // traitement ssi base marquée
    if (pTmgrTls->isRegisterTainted<64>(baseReg)) 
    {
        _LOGTAINT("B");
        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(pTmgrTls->getRegisterTaint<64>(baseReg, baseRegValue));
    }
} // computeEA_B(64bits)

void UTILS::computeEA_ISD(FUNCARGS_ISD)
{
// pour construire l'EA, on additionne deux entités : index*scale et displ
//  SI INDEX MARQUE  IS = index*scale (via SHL); 
//  EA = ADD ou SUB(IS, displ)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
   
    // traitement ssi index marqué, sinon ne rien faire
    if (pTmgrTls->isRegisterTainted<64>(indexReg)) 
    {
        _LOGTAINT("ISD");
   
        // valeur du déplacement (avec scale = 2^depl)
        UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
        // 1) opération index*scale traité comme un SHL car déplacement multiple de 2 
        // source 1 : le registre d'index (forcément marqué)
        // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
        TaintQwordPtr tqwISptr = std::make_shared<TaintQword>
            (X_SHL, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)),
            ObjectSource(8, shiftValue)
            );  
            
        // 2) opération IS +/- displ et stockage dans TaintManager
        Relation rel    = (displ > 0) ? X_ADD : X_SUB;
        UINT32 absDispl = abs(displ);

        // stockage dans TaintManager
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(rel, 
            ObjectSource(tqwISptr), 
            ObjectSource(64, absDispl)));
    }
} // computeEA_ISD(64bits)

void UTILS::computeEA_IS(FUNCARGS_IS)
{
    // SI INDEX MARQUE  EA = index*scale (via SHL)
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
   
    // traitement ssi index marqué, sinon ne rien faire
    if (pTmgrTls->isRegisterTainted<64>(indexReg)) 
    {
        _LOGTAINT("IS");
   
        // valeur du déplacement (avec scale = 2^depl)
        UINT32 shiftValue = (scale == 2) ? 1 : ((scale == 4) ? 2 : 3);
                
        // opération index*scale traité comme un SHL car déplacement multiple de 2 
        // source 1 : le registre d'index (forcément marqué)
        // source 2 : shiftValue (sur 8 bits, comme tous les shifts)
        pTmgrTls->storeTaintEffectiveAddress(std::make_shared<TaintQword>(
            X_SHL, 
            ObjectSource(pTmgrTls->getRegisterTaint<64>(indexReg, indexRegValue)),
            ObjectSource(8, shiftValue))); 
    }
} // computeEA_IS(64bits)

#endif
