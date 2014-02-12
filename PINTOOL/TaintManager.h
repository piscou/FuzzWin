#pragma once

#include "pintool.h"
#include "TaintObject.h"
#include "ObjectSource.h"

#include <map>
#include <stack> // enregistrement des adresses de retour lors des CALL/RET
#include <regex> // parsing des octets à suivre en marquage

// position des flags
enum FLAGS_INDEX
{
    CARRY_FLAG      = 0,    /*!< Carry Flag  */
    PARITY_FLAG     = 2,    /*!< Parity Flag */
    AUXILIARY_FLAG  = 4,    /*!< Auxiliary Carry Flag */
    ZERO_FLAG       = 6,    /*!< Zero Flag */
    SIGN_FLAG       = 7,    /*!< Sign Flag */
    DIRECTION_FLAG  = 10,   /*!< Direction Flag */
    OVERFLOW_FLAG   = 11,   /*!< Overflow Flag */
};

// type d'adressage indirect utilisé dans une instruction
// sert a déterminer les arguments passés aux fonctions d'analyse
enum KIND_OF_EFFECTIVE_ADDRESS
{
    EA_IMMEDIATE,         /*!< cas ou l'adresse est juste une valeur : peu interessant */
    EA_BASE,              /*!< base, sans index ni déplacement    */
    EA_BASE_DISPL,        /*!< base, sans index, déplacement non nul  */
    // les cas INDEX et INDEX_DISPL sont impossibles (dans ce cas c'est un registre de base)
    EA_INDEX_SCALE,       /*!< index, scale != 1, sans base ni déplacement */
    EA_INDEX_SCALE_DISPL, /*!< index, scale != 1, sans base, déplacement non nul */
    EA_BASE_INDEX,        /*!< base, index, pas de scale ni déplacement */
    EA_BASE_INDEX_DISPL,  /*!< base, index, pas de scale, déplacement non nul */
    EA_BASE_INDEX_SCALE,  /*!< base, index, scale != 1, pas de scale ni déplacement */
    EA_BASE_INDEX_SCALE_DISPL,  /*!< base, index, scale != 1, déplacement non nul */
};

// extraction de l'octet n° "index" de la valeur "value"
static inline UINT32 EXTRACTBYTE(ADDRINT value, UINT32 index) 
{
    return (static_cast<UINT32>(0xff & (value >> (index << 3)))); 
}

// extraction du bit n° "index" de la valeur "value"
static inline UINT32 EXTRACTBIT(ADDRINT value, UINT32 index) 
{
    return (static_cast<UINT32>(0x1 & (value >> index))); 
}

// structure de sauvegarde des adresses de retour des fonctions
// TODO : analyse à faire en option choisie par l'utilisateur
typedef struct
{
    ADDRINT espAddress;     // valeur du registre de pile
    ADDRINT returnValue;    // valeur de retour (déréférencée de la pile)
} protectedAddresses;

typedef struct 
{
    bool isREPZ;        // VRAI si REPZ, faux si REPNZ
    bool isRegTainted;  // Vrai si registre AL/AX/EAX/RAX marqué
    TaintPtr tPtr;      // objet marqué représentant AL/AX/EAX/RAX
    ADDRINT regValue;   // Valeur de AL/AX/EAX/RAX
    ADDRINT instrPtr;   // adresse de l'instruction SCAS
} StringOpInfo;

/************************************/
/** CLASSES DE GESTION DU MARQUAGE **/
/************************************/
class TaintManager_Global;
class TaintManager_Thread;

// TaintManager_Global = gestion de la mémoire et des objets globaux (ex : octets à suivre en marquage)
// étant une classe commune à tous les threads, les fonctions membres utilisent PIN_LOCK.
class TaintManager_Global
{

private:
    // Marquage de la mémoire : indépendante des threads
    std::map<ADDRINT, TaintBytePtr> _memoryPtrs;

    // offsets des octets déjà lus dans le fichier-cible. Evite la déclaration de plusieurs
    // objets TaintByte représentant le même octet dans le fichier. Indépendante des threads
    std::map<UINT32, TaintBytePtr> _offsets;

    // offset des octets à surveiller en marquage. Passé en argument d'entrée au pintool
    // stockage des valeurs sous forme d'intervalle (min,max), min pouvant etre égal à max
    std::vector<std::pair<UINT32, UINT32>> _bytesToTaint;

public:
    /***********************************/
    /** STOCKAGE DES OCTETS A MARQUER **/
    /***********************************/
    void setBytesToTaint(const std::string &bytesString)
    {
        // si "all", tous les octets seront à marquer => pas besoin de remplir le vecteur
        if (bytesString != "all") 
        {
            // expression réguliere pour octets à marquer
            // option qui permet de spécifier uniquement certains octets à suivre en marquage. 
            // type formulaire d'impression (1,3,5-30,34,...)
            // séparation par virgules ou point-virgules, 
            // pas d'espaces entre chiffres (sinon fait planter le parsing de argv)
            // syntaxe de la regex: ,(présent ou non)'nb'-(présent ou non)'nb'
            const std::regex bytesModel("[,;]?\\s*(\\d+)\\s*-?\\s*([0-9]+)?", std::regex::ECMAScript); 
            int tokens[2] = {1,2};
            
            // itérateur de type string sur chaque groupe d'octets qui matche
            std::sregex_token_iterator it(bytesString.begin(), bytesString.end(), bytesModel, tokens);
            std::sregex_token_iterator end;
            
            while (it != end) 
            {
                int minBound, maxBound;
                
                // 1ere valeur = borne minimale (tjs présente)
                minBound = std::stoi(it->str());  
                ++it; 

                // 2eme valeur = si présente ca sera la borne maximale
                // sinon reprendre la borne minimale
                if (it->matched) 
                {
                    maxBound = std::stoi(it->str());
                    // juste pour s'assurer que le minimum l'est bien...
                    if (maxBound < minBound) std::swap(maxBound, minBound);
                }
                else maxBound = minBound;
                ++it;  

                // stockage du couple dans la liste
                this->_bytesToTaint.push_back(std::make_pair(minBound, maxBound));
            }
        }
    }

    /*******************************/
    /** INTERROGATION DU MARQUAGE **/
    /*******************************/

    // renvoie TRUE si tout ou partie de la plage [address, address+size] est marquée
    template<UINT32 lengthInBits> bool isMemoryTainted(ADDRINT address) const 
    {
        bool result = false;
        ADDRINT lastAddress = address + (lengthInBits >> 3);

        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        while (address < lastAddress)
        { 
            if (this->_memoryPtrs.find(address++) != this->_memoryPtrs.end())
            {
                result = true;
                break;
            }
        }
        PIN_ReleaseLock(&g_lock);

        // si on arrive ici c'est que aucun emplacement mémoire n'est marqué
        return (result); 
    }

    // spécialisation 8bits
    template<> bool isMemoryTainted<8>(ADDRINT address) const 
    {
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        auto it    = this->_memoryPtrs.find(address);
        auto itEnd = this->_memoryPtrs.end();
        PIN_ReleaseLock(&g_lock);

        return (it != itEnd);
    }

    /******************************/
    /** RECUPERATION DU MARQUAGE **/
    /******************************/

    // renvoie un objet représentant le marquage de la plage d'adresses
    template<UINT32 lengthInBits> TAINT_OBJECT_PTR getMemoryTaint(ADDRINT address) const
    { 
        static_assert((lengthInBits % 8 == 0), "taille non multiple de 8 bits");
        TaintObject<lengthInBits> result(CONCAT);
        ADDRINT lastAddress = address + (lengthInBits >> 3);
        
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        auto itEnd = this->_memoryPtrs.end();
        
        while (address < lastAddress) 
        {
            auto it = this->_memoryPtrs.find(address);
            if (it != itEnd) // si une entrée à été trouvée => adresse marquée
            {       
                result.addSource(it->second);
            }
            else result.addConstantAsASource<8>(getMemoryValue<8>(address));

            address++;
        }
        PIN_ReleaseLock(&g_lock);
        return (MK_TAINT_OBJECT_PTR(result));
    }

    // spécialisation pour le cas 8 bits
    template<> TaintBytePtr getMemoryTaint<8>(ADDRINT address) const
    {
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        auto it    = this->_memoryPtrs.find(address);
        auto itEnd = this->_memoryPtrs.end();
        PIN_ReleaseLock(&g_lock);

        return ( (it == itEnd) ? nullptr : it->second);
    }

    // renvoi d'une copie de la MAP : sert aux statistiques de fin de programme
    std::map<ADDRINT, TaintBytePtr> getSnapshotOfTaintedLocations() const
    { return this->_memoryPtrs; }
    
    /*******************************/
    /** CREATION D'OBJETS SOURCES **/
    /*******************************/

    // création de "nb" nouveaux TaintBytes initiaux à la position "offset" du fichier
    // et marquage de la mémoire pointée par "buffer"
    void createNewSourceTaintBytes(ADDRINT buffer, UINT32 nb, UINT32 offset) 
    {
        TaintBytePtr tbPtr;
        ADDRINT endOfBuffer = buffer + nb;  // dernier octet du buffer
        
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale

        // Si le vecteur est vide, tous les octets de la source doivent être marqué
        // sinon il faudra vérifier que chaque octet est dans les intervelles à suivre
        bool mustAllBytesBeTainted = this->_bytesToTaint.empty(); 

        // création de 'nb' objets à partir de l'adresse 'buffer'
        for (ADDRINT endOfBuffer = buffer + nb ; buffer < endOfBuffer ; ++buffer, ++offset)
        {
            // vérification du fait que cet octet doit être marqué
            if (!mustAllBytesBeTainted)
            {
                // recherche de la présence de l'offset dans l'un des intervalles
                // par défaut on considère qu'il ne l'est pas
                bool isThisByteToBeTainted = false;
                auto it    = this->_bytesToTaint.begin();
                auto itEnd = this->_bytesToTaint.end();
                while (it != itEnd)
                {
                    // supérieur ou égal à borne min et inférieur ou égal à max
                    if ((offset >= it->first) && (offset <= it->second))
                    {
                        isThisByteToBeTainted = true;
                        break;
                    }
                    ++it;
                }
                // si offset non trouvé : ne rien marquer, poursuivre au prochain octet
                if (!isThisByteToBeTainted) continue;
            }

            auto it = this->_offsets.find(offset);
            // si aucune entrée : lecture d'un nouvel offset dans le fichier
            if (it == this->_offsets.end()) 
            {
                // création du nouvel objet 8bits et ajout de son offset comme source
                tbPtr = std::make_shared<TaintByte>(BYTESOURCE, ObjectSource(32, offset));
                // Ajout de cet objet dans la liste des octets déjà lus dans la source
                this->_offsets.insert(pair<UINT32, TaintBytePtr>(offset, tbPtr));
            }
            // sinon cet octet a déjà été lu : le TaintByte est déjà créé
            else tbPtr = it->second;     

            // marquage de la mémoire
            this->_memoryPtrs[buffer] = tbPtr;          
        }
        PIN_ReleaseLock(&g_lock);

    } // createNewSourceTaintBytes

    /*****************************************/
    /** FONCTIONS DE MARQUAGE DE LA MEMOIRE **/
    /*****************************************/

    // marquage de 'lengthInBits' octets avec l'objet 'tPtr' à partir de l'adresse 'address'
    // si 'tPtr' est nullptr, provoque le démarquage des 'lengthInBits' octets
    template<UINT32 lengthInBits> void updateMemoryTaint
        (ADDRINT address, const TAINT_OBJECT_PTR &tPtr) 
    {
        static_assert((lengthInBits & 0x7) == 0, "taille memoire non valide");           
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        
        if (!tPtr) this->unTaintMemory<lengthInBits>(address);
        else
        {
            ObjectSource objSrc(tPtr);
            // création des taintBytes extraits de l'objet pour affectation
            for (UINT32 i = 0 ; i < (lengthInBits >> 3) ; ++i, ++address) 
            { 
                // extraction de 'objSrc' de l'octet (8bits) n°i et affectation à l'adresse adéquate
                this->_memoryPtrs[address] = std::make_shared<TaintByte>
                    (EXTRACT, objSrc, ObjectSource(8, i));
            }
        }

        PIN_ReleaseLock(&g_lock);
    }

    // spécialisation pour le cas 8bits
    template<> void updateMemoryTaint<8>(ADDRINT address, const TaintBytePtr &tbPtr) 
    { 
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        if (!tbPtr) this->_memoryPtrs.erase(address);
        else        this->_memoryPtrs[address] = tbPtr;
        PIN_ReleaseLock(&g_lock);
    }

    /****************************/
    /** FONCTION DE DEMARQUAGE **/
    /****************************/
   
    // Efface le marquage de la plage [address, address + lengthInBits];
    template<UINT32 lengthInBits> void unTaintMemory(ADDRINT address) 
    {            
        ADDRINT lastAddress = address + (lengthInBits >> 3);
        PIN_GetLock(&g_lock, 0); // obligatoire car classe globale
        while (address < lastAddress) this->_memoryPtrs.erase(address++);
        PIN_ReleaseLock(&g_lock);
    }
};


// TaintManager_Thread = gestion des registres et des fonctions spécifiques
// (suivi des CALL/RET) qui SONT DEPENDANTES DES THREADS
class TaintManager_Thread
{

private:
    // Marquage des registres d'usage général (GP) représentés en sous-registres de 8 bits
    TaintBytePtr _registers8Ptr[regIndexLAST + 1][BYTEPARTS];

    // marquage des registres "entiers" de 16, 32 (et 64bits)
    // lors de la récupération du marquage d'un registre de plus de 8bits
    // on testera d'abord si le registre n'est pas marqué avec un objet de taille supérieure
    // afin de ne pas recréer une concaténation d'objets 8 bits alors que l'objet existe
    // l'index dans le tableau est celui du registre "plein" (32 ou 64bits)
    // ex : le marquage de R10W se trouvera à registres64[rR10]
    TaintWordPtr  _registers16Ptr[regIndexLAST + 1];
    TaintDwordPtr _registers32Ptr[regIndexLAST + 1];
#if TARGET_IA32E
    TaintQwordPtr _registers64Ptr[regIndexLAST + 1];
#endif

    // cas du registre Eflags : marquage niveau bit 
    TaintBitPtr  _cFlagPtr, _pFlagPtr, _aFlagPtr, _zFlagPtr, _sFlagPtr, _oFlagPtr;

    // enregistrement des adresses de retour mises sur la pile lors des instructions "CALL"
    // lors d'un "RET", l'adresse de retour sera comparée à celle présente sur la pile
    // s'ils sont différentes => exploitation possible. 
    // ne se limite pas aux adresse de retour marquées (ex : buff overfl avec débordement tableau)
    std::stack<protectedAddresses> _addressProtection;

    // Stockage des informations récurrentes lors des opérations de chaines ("STRINGOP")
    StringOpInfo _strInfo; 

    // stockage de l'objet permettant de calculer une addresse effective 
    // (taille selon architecture)
#if TARGET_IA32
    TaintDwordPtr _effectiveAddressPtr; // 32bits
#else
    TaintQwordPtr _effectiveAddressPtr; // 64bits
#endif

public:
    TaintManager_Thread()  {}
    ~TaintManager_Thread() {}

    /**************************************************/
    /** GESTION DU MARQUAGE DES ADDRESSES EFFECTIVES **/
    /**************************************************/

#if TARGET_IA32
    // mise en cache d'un objet calculant une addresse effective (32bits)
    void storeTaintEffectiveAddress(TaintDwordPtr tdwPtr)
    { this->_effectiveAddressPtr = tdwPtr; }

    // récupération de l'objet mis en cache
    TaintDwordPtr getTaintEffectiveAddress() const
    { return (this->_effectiveAddressPtr); }
#else
    // mise en cache d'un objet calculant une addresse effective (64bits)
    void storeTaintEffectiveAddress(TaintQwordPtr tqwPtr)
    { this->_effectiveAddressPtr = tqwPtr; }

    // récupération de l'objet mis en cache
    TaintQwordPtr getTaintEffectiveAddress() const
    { return (this->_effectiveAddressPtr); }
#endif

    // spécifie que la valeur de l'adresse effective n'est pas marquée
    // fonction appelée systématiquement après le traitement de l'instruction
    void clearTaintEffectiveAddress() 
    { this->_effectiveAddressPtr.reset(); }

    /*******************************/
    /** INTERROGATION DU MARQUAGE **/
    /*******************************/

    // renvoie TRUE tout ou partie du registre reg (de type PIN) est marqué
    template<UINT32 lengthInBits> bool isRegisterTainted(REG reg) const
    {
        REGINDEX regIndex = getRegIndex(reg);
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur isRegisterTainted non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        bool result = false;
        for (UINT32 i = 0 ; i < (lengthInBits >> 3) ; ++i) 
        { 
            if ((bool) this->_registers8Ptr[regIndex][i])
            {
                result = true;
                break;
            }
        }
        // si on arrive ici c'est que aucune partie de registre n'est marqué
        return (result); 
    }

    // cas particulier 8 bits : partie haute ou basse
    template<> bool isRegisterTainted<8>(REG reg) const 
    {
        REGINDEX regIndex = getRegIndex(reg);
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur isRegisterTainted non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif
        
        return (REG_is_Upper8(reg) 
            ? (bool) this->_registers8Ptr[regIndex][1] 
            : (bool) this->_registers8Ptr[regIndex][0]);
    }

    // cas d'une partie spécifique du registre
    bool isRegisterPartTainted(REGINDEX regIndex, UINT32 regPart) const 
    { 
        return ((bool) this->_registers8Ptr[regIndex][regPart]); 
    }

    // renvoie TRUE si le flag est marqué
    bool isCarryFlagTainted() const    { return ((bool) this->_cFlagPtr); }
    bool isParityFlagTainted() const   { return ((bool) this->_pFlagPtr); }
    bool isAuxiliaryFlagTainted() const{ return ((bool) this->_aFlagPtr); }
    bool isZeroFlagTainted() const     { return ((bool) this->_zFlagPtr); }
    bool isSignFlagTainted() const     { return ((bool) this->_sFlagPtr); }
    bool isOverflowFlagTainted() const { return ((bool) this->_oFlagPtr); }

    /******************************/
    /** RECUPERATION DU MARQUAGE **/
    /******************************/

    // renvoie un objet représentant le marquage d'un registre 
    // template entièrement spécialisé pour prendre en compte
    // les registres 8/16/32/64bits "entiers"
    template<UINT32 lengthInBits> TAINT_OBJECT_PTR getRegisterTaint(REG reg, ADDRINT regValue) 
    {
        static_assert((lengthInBits % 8 == 0), "registre non multiple de 8 bits");
    }

    // cas 8bits : appel de la fonction surchargée à 1 seul paramètre
    template<> TaintBytePtr getRegisterTaint<8>(REG reg8, ADDRINT unUsed)
    {
        return (this->getRegisterTaint(reg8));
    }
    
    // cas 16 bits : renvoi du TaintWord correspondant (si existant) 
    // ou concaténation des 2 registres 8 bits 
    template<> TaintWordPtr getRegisterTaint<16>(REG reg16, ADDRINT reg16Value)
    {
        REGINDEX regIndex = getRegIndex(reg16);
        
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur getRegisterTainted non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // test du marquage 16 bits. Si absent => créer un nouvel objet
        if (!(bool) this->_registers16Ptr[regIndex])
        {
            TaintWord result(CONCAT);
            for (UINT32 i = 0 ; i < 2 ; ++i) 
            {
                // si la partie du registre est marqué, ajout de cet objet à la concaténation   
                if ((bool) this->_registers8Ptr[regIndex][i]) 
                {
                    result.addSource(this->_registers8Ptr[regIndex][i]);
                }
                // sinon, ajout d'une source de type immédiate
                else result.addConstantAsASource<8>(EXTRACTBYTE(reg16Value, i));
            }
            // association de l'objet nouvellement créé au registre 16bits
            this->_registers16Ptr[regIndex] = std::make_shared<TaintWord>(result);
        }
        return (this->_registers16Ptr[regIndex]);
    }

    // cas 32 bits : renvoi du TaintDword correspondant (si existant) 
    // ou concaténation des 4 registres 8 bits 
    template<> TaintDwordPtr getRegisterTaint<32>(REG reg32, ADDRINT reg32Value)
    {
        REGINDEX regIndex = getRegIndex(reg32);      
        
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur getRegisterTainted non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // test du marquage 32 bits. si aucune variable => la fabriquer
        if (!(bool) this->_registers32Ptr[regIndex])
        {
            TaintDword result(CONCAT);
            for (UINT32 i = 0 ; i < 4 ; ++i) 
            {
                // si la partie du registre est marqué, ajout de cet objet 
                // à la concaténation   
                if ((bool) this->_registers8Ptr[regIndex][i]) 
                {
                    result.addSource(this->_registers8Ptr[regIndex][i]);
                }
                // sinon, ajout d'une source de type immédiate
                else result.addConstantAsASource<8>(EXTRACTBYTE(reg32Value, i));
            }
            
            // association de l'objet nouvellement créé au registre 32bits
            this->_registers32Ptr[regIndex] = std::make_shared<TaintDword>(result);
        }
        // retour de l'objet 32bits existant ou créé
        return (this->_registers32Ptr[regIndex]);
    }
 
#if TARGET_IA32E
    // cas 64 bits : renvoi du TaintQword correspondant (si existant) 
    // ou concaténation des 8 registres 8 bits 
    template<> TaintQwordPtr getRegisterTaint<64>(REG reg64, ADDRINT reg64Value)
    {
        REGINDEX regIndex = getRegIndex(reg64);

        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur getRegisterTainted non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // test du marquage 32 bits
        if (!(bool) this->_registers64Ptr[regIndex])
        {
            TaintQword result(CONCAT);
            for (UINT32 i = 0 ; i < 8 ; ++i) 
            {
                // si la partie du registre est marqué, ajout de cet objet 
                // à la concaténation   
                if ((bool) this->_registers8Ptr[regIndex][i]) 
                {
                    result.addSource(this->_registers8Ptr[regIndex][i]);
                }
                // sinon, ajout d'une source de type immédiate
                else result.addConstantAsASource<8>(EXTRACTBYTE(reg64Value, i));
            }
        
            // association de l'objet nouvellement créé au registre 64bits
            this->_registers64Ptr[regIndex] = std::make_shared<TaintQword>(result);
        }
        return (this->_registers64Ptr[regIndex]);
    }
#endif

    // renvoie un objet représentant le marquage d'un registre 8 bits
    // surcharge du template normal (passage d'un seul paramètre)
    TaintBytePtr getRegisterTaint(REG reg) const
    { 
        UINT32 regPart = REG_is_Upper8(reg) ? 1 : 0;
        REGINDEX regIndex = getRegIndex(reg);

        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur getRegisterTainted non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif
        
        return (this->_registers8Ptr[regIndex][regPart]);
    }

    // renvoie le marquage d'une partie de registre
    TaintBytePtr getRegisterPartTaint(REGINDEX regIndex, UINT32 regPart) const  
    {  return (this->_registers8Ptr[regIndex][regPart]); }

    // renvoie le marquage correspondant aux flags
    TaintBitPtr getTaintCarryFlag()     const   { return (this->_cFlagPtr); }
    TaintBitPtr getTaintParityFlag()    const   { return (this->_pFlagPtr); }
    TaintBitPtr getTaintAuxiliaryFlag() const   { return (this->_aFlagPtr); }
    TaintBitPtr getTaintZeroFlag()      const   { return (this->_zFlagPtr); }
    TaintBitPtr getTaintSignFlag()      const   { return (this->_sFlagPtr); }
    TaintBitPtr getTaintOverflowFlag()  const   { return (this->_oFlagPtr); }

    /*****************************************/
    /** FONCTIONS DE MARQUAGE DES REGISTRES **/
    /*****************************************/

    // associe au registre "regIndex", partie "regPart"
    // l'objet TaintByte fourni
    void updateTaintRegisterPart(REGINDEX regIndex, UINT32 regPart, const TaintBytePtr &tbPtr) 
    {
        this->_registers8Ptr[regIndex][regPart] = tbPtr;
        // si un registre plein était présent (16, ou 32, ou 64)
        // effacer le marquage, car une partie 8 bits a été modifiée
        this->_registers16Ptr[regIndex].reset();
        this->_registers32Ptr[regIndex].reset();
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
    }

    // mise à jour du marquage du registre avec l'objet fourni
    // spécialisation complete du template pour marquer les registres "entiers"
    template<UINT32 lengthInBits> 
    void updateTaintRegister(REG reg, const TAINT_OBJECT_PTR &tPtr)
    {  static_assert((lengthInBits % 8 == 0), "registre non valide");  }

    // cas 8bits
    template<> void updateTaintRegister<8>(REG reg8, const TaintBytePtr &tbPtr) 
    {
        REGINDEX regIndex = getRegIndex(reg8);

        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur updateTaintRegister non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // si un registre plein était présent (16, ou 32, ou 64)
        // effacer le marquage, car une partie 8 bits a été modifiée
        this->_registers16Ptr[regIndex].reset();
        this->_registers32Ptr[regIndex].reset();
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
        // marquage
        this->_registers8Ptr[regIndex][(REG_is_Upper8(reg8)) ? 1 : 0] = tbPtr;
    }

    // cas 16bits
    template<> void updateTaintRegister<16>(REG reg16, const TaintWordPtr &twPtr) 
    {
        REGINDEX regIndex = getRegIndex(reg16);

        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur updateTaintRegister non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // si un registre plein était présent : effacer le marquage
        // car une partie a été modifiée
        this->_registers32Ptr[regIndex].reset();
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
        
        // marquage d'abord de la partie 16 bits, 
        this->_registers16Ptr[regIndex] = twPtr;
        // puis de chaque partie de 8 bits
        ObjectSource objSrc(twPtr); 
        // création des taintBytes extraits de l'objet pour affectation
        for (UINT32 i = 0 ; i < 2 ; ++i) 
        {
            // objet duquel l'octet est extrait (sous forme de source) + index d'extraction
            this->_registers8Ptr[regIndex][i] = std::make_shared<TaintByte>
                (EXTRACT, objSrc, ObjectSource(8, i));
        }
    }

    // cas 32bits
    template<> void updateTaintRegister<32>(REG reg32, const TaintDwordPtr &tdwPtr) 
    {
        REGINDEX regIndex = getRegIndex(reg32);
        
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur updateTaintRegister non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif
        
        // si un registre plein était présent : effacer le marquage, car une partie a été modifiée
        this->_registers16Ptr[regIndex].reset();        
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
        
        // marquage d'abord de la partie 32 bits, 
        this->_registers32Ptr[regIndex] = tdwPtr;
        // puis de chaque partie de 8 bits
        ObjectSource objSrc(tdwPtr); 
        // création des taintBytes extraits de l'objet pour affectation
        for (UINT32 i = 0 ; i < 4 ; ++i) 
        {
            // objet duquel l'octet est extrait (sous forme de source) + index d'extraction
            this->_registers8Ptr[regIndex][i] = std::make_shared<TaintByte>
                (EXTRACT, objSrc, ObjectSource(8, i)); 
        }
    }

#if TARGET_IA32E
    // cas 64bits
    template<> void updateTaintRegister<64>(REG reg64, const TaintQwordPtr &tqwPtr) 
    {
        REGINDEX regIndex = getRegIndex(reg64);
        
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur updateTaintRegister non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif
        
        // si un registre plein de 16 ou 32bits était présent 
        // effacer le marquage, car une partie a été modifiée
        this->_registers16Ptr[regIndex].reset();  
        this->_registers32Ptr[regIndex].reset();

        // marquage d'abord de la partie 64 bits, 
        this->_registers64Ptr[regIndex] = tqwPtr;
        // puis de chaque partie de 8 bits
        ObjectSource objSrc(tqwPtr); 
        // création des taintBytes extraits de l'objet pour affectation
        for (UINT32 i = 0 ; i < 8 ; ++i) 
        {
             // objet duquel l'octet est extrait (sous forme de source) + index d'extraction
            this->_registers8Ptr[regIndex][i] = std::make_shared<TaintByte>
                (EXTRACT, objSrc, ObjectSource(8, i));
        }
    }
#endif

    /*************************************/
    /** FONCTIONS DE MARQUAGE DES FLAGS **/
    /*************************************/

    void updateTaintCarryFlag  (const TaintBitPtr &ptr)  { this->_cFlagPtr = ptr;}
    void updateTaintParityFlag (const TaintBitPtr &ptr)  { this->_pFlagPtr = ptr;}
    void updateTaintAuxiliaryFlag(const TaintBitPtr &ptr){ this->_aFlagPtr = ptr;}
    void updateTaintZeroFlag   (const TaintBitPtr &ptr)  { this->_zFlagPtr = ptr;}
    void updateTaintSignFlag   (const TaintBitPtr &ptr)  { this->_sFlagPtr = ptr;}
    void updateTaintOverflowFlag(const TaintBitPtr &ptr) { this->_oFlagPtr = ptr;}

    /*****************************/
    /** FONCTIONS DE DEMARQUAGE **/
    /*****************************/

    // Efface le marquage d'une partie de registre
    void unTaintRegisterPart(REGINDEX regIndex, UINT32 regPart) 
    { 
        // effacement de la partie 8 bits (et forcement des registres 16/32/64)
        this->_registers8Ptr[regIndex][regPart].reset();  
        this->_registers16Ptr[regIndex].reset();
        this->_registers32Ptr[regIndex].reset();
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
    }
    
    // Efface le marquage du registre fourni en argument
    template<UINT32 lengthInBits> void unTaintRegister(REG reg)  
    { 
        REGINDEX regIndex = getRegIndex(reg);
        
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur unTaintRegister non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // effacement des parties 8 bits 
        for (UINT32 i = 0 ; i < (lengthInBits >> 3) ; ++i)   this->_registers8Ptr[regIndex][i].reset();
        
        // effacement forcement des registres 16/32/64
        this->_registers16Ptr[regIndex].reset();
        this->_registers32Ptr[regIndex].reset();
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
    }

    // spécialisation pour le cas 8bits
    template<> void unTaintRegister<8>(REG reg)  
    { 
        REGINDEX regIndex = getRegIndex(reg);
        UINT32 regPart =  REG_is_Upper8((REG)reg) ? 1 : 0;
        
        #if DEBUG
        if (regIndex == regIndexINVALID)
        {
            g_debug << "Erreur unTaintRegister non géré" << std::endl;
            PIN_ExitApplication(EXIT_FAILURE);
        }
        #endif

        // effacement des registres 8/16/32/64
        this->_registers8Ptr[regIndex][regPart].reset();
        this->_registers16Ptr[regIndex].reset();
        this->_registers32Ptr[regIndex].reset();
        #if TARGET_IA32E
        this->_registers64Ptr[regIndex].reset();
        #endif
    }
    
    // démarque le flag
    void unTaintCarryFlag()    { this->_cFlagPtr.reset(); }
    void unTaintParityFlag()   { this->_pFlagPtr.reset(); }
    void unTaintAuxiliaryFlag(){ this->_aFlagPtr.reset(); }
    void unTaintZeroFlag()     { this->_zFlagPtr.reset(); }
    void unTaintSignFlag()     { this->_sFlagPtr.reset(); }
    void unTaintOverflowFlag() { this->_oFlagPtr.reset(); }

    // supprime le marquage de tous les flags
    void unTaintAllFlags() 
    {
        this->_cFlagPtr.reset();      
        this->_pFlagPtr.reset();
        this->_aFlagPtr.reset();      
        this->_zFlagPtr.reset();
        this->_sFlagPtr.reset();   
        this->_oFlagPtr.reset();
    }

    /***************************/
    /** CONTROLE DES CALL/RET **/
    /***************************/
    void pushProtectedAdresses(protectedAddresses pa) 
    { this->_addressProtection.push(pa);}

    bool isProtectedAddressesEmpty() 
    { return (this->_addressProtection.empty());} 

    protectedAddresses getProtectedAdresses()
    {         
        // remplacer par une copie de chaque élément avec déclaration
        protectedAddresses temp = this->_addressProtection.top();
        this->_addressProtection.pop();
        return (temp);
    }

    /****************************/
    /** MISE EN CACHE STRINGOP **/
    /****************************/
    
    void storeStringOpInfo(const StringOpInfo &s) 
    { this->_strInfo = s;}

    StringOpInfo& getStoredStringOpInfo()  
    { return this->_strInfo; }

};

// pointeur global vers classe de gestion du marquage mémoire
extern TaintManager_Global *pTmgrGlobal;

// fonction inline pour récupérer la classe de marquage locale stockée dans la TLS
static inline TaintManager_Thread* getTmgrInTls(THREADID tid)
{
    return (static_cast<TaintManager_Thread*>(PIN_GetThreadData(g_tlsKeyTaint, tid)));
}
