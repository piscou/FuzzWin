#include "fuzzwin_algo.h"

OSTYPE getNativeArchitecture()
{
    OSTYPE osType = HOST_UNKNOWN;

    // la fonction GetNativeSystemInfo retourne une structure avec notamment
    // 'wProcessorArchitecture' qui détermine si OS 32 ou 64bits 
    SYSTEM_INFO si;
    ZeroMemory(&si, sizeof(si));
    GetSystemInfo(&si);

    // GetVersionEx récupère la version de l'OS pour fixer le numéro des syscalls
    // la structure OSVERSIONINFOEX contient ce que l'on cherche à savoir
    OSVERSIONINFOEX osvi;
    ZeroMemory(&osvi, sizeof(osvi));
    osvi.dwOSVersionInfoSize = sizeof(OSVERSIONINFOEX);
    GetVersionEx(reinterpret_cast<OSVERSIONINFO*>(&osvi));
    // version = 10*major + minor ; permet de comparer tout de suite les nombres
    int osVersion = (10 * osvi.dwMajorVersion) + osvi.dwMinorVersion;
    
    // isWow64Process détermine si fuzzwin fonctionne en émulation 64bits.
    BOOL bIsWow64 = FALSE;
    IsWow64Process(GetCurrentProcess(), &bIsWow64);

    // Architecture de l'OS = 64 bits, ou bien émulation (Wow64)
    if ((PROCESSOR_ARCHITECTURE_AMD64 == si.wProcessorArchitecture)	|| bIsWow64)
    {
        // Avant Windows 8 (version 6.2), tous les OS 64bits
        // ont les mêmes tables pour les syscalls
        if (osVersion < 62)         osType = HOST_X64_BEFORE_WIN8;

        // Windows 8 : version 6.2
        else if (62 == osVersion)   osType = HOST_X64_WIN80;

        // pour Windows 8.1, getVersionEx est déprécié => TODO FAIRE AUTREMENT
        else if (63 == osVersion)   osType = HOST_X64_WIN81;
    }
    else if (PROCESSOR_ARCHITECTURE_INTEL == si.wProcessorArchitecture)	
    {
        switch (osVersion)	
        {
        case 50:  // Version 5.0 = Windows 2000
            osType = HOST_X86_2000;
            break;

        case 51:  // Version 5.1 = Windows XP
            osType = HOST_X86_XP;
            break;

        case 52:  // Version 5.2 = Server 2003. XP 64bits n'est pas considéré car on est en 32bits
            osType = HOST_X86_2003;
            break;

        case 60:  // Version 6.0 = Vista ou Server 2008
            if (VER_NT_WORKSTATION == osvi.wProductType) // Vista => tester le cas SP0
            {
                // le syscall 'NtSetInformationFile' diffère entre SP0 et les autres SP
                // on teste donc si un service pack est présent
                osType = (osvi.wServicePackMajor) ? HOST_X86_VISTA : HOST_X86_VISTA_SP0;
            }
            else osType = HOST_X86_2008;
            break;
       
        case 61:  // Version 6.1 = Seven ou Server 2008 R2
            osType = (VER_NT_WORKSTATION == osvi.wProductType) ? HOST_X86_SEVEN : HOST_X86_2008_R2;
            break;
     
        case 62:  // Version 6.2 = Windows 8 ou Server 2012
            osType = (VER_NT_WORKSTATION == osvi.wProductType) ? HOST_X86_WIN80 : HOST_X86_2012;
            break;

        case 63:  // Version 6.3 = Windows 8.1 ou Server 2012R2 (à voir car GetVersionEx dépréciée)
            osType = (VER_NT_WORKSTATION == osvi.wProductType) ? HOST_X86_WIN81 : HOST_X86_2012_R2;
            break;
      
        default:  // OS non reconnu donc non supporté 
            break; 
        }
    }
    return (osType);
} // getNativeArchitecture

int getKindOfExecutable(const std::string &targetPath)
{
    DWORD kindOfExe = 0;
    BOOL  result = GetBinaryType((LPCSTR) targetPath.c_str(), &kindOfExe);
    
    // erreur si fichier non exécutable ou si non trouvé
    if (!result) return (-1);
    else         return (kindOfExe);
} // getKindOfExecutable

std::string getAbsoluteFilePath(const std::string &s)
{
    char absolutepath[MAX_PATH];
    LPSTR* a = nullptr;

    // transformation du chemin relatif en chemin absolu
    DWORD retval = GetFullPathName((LPCSTR) s.c_str(), MAX_PATH, absolutepath, a);

    if (!retval) return (std::string()); // erreur (fichier non présent ?)
    else         return (std::string(absolutepath));
}

/*************************************************/
/* CLASSES DE BASE (DERIVEES DANS CMDLINE ET GUI */
/*************************************************/

/*********************************************/
/* CINPUT : description d'une entrée de test */
/*********************************************/

CInput::CInput(const std::string &firstInputPath, bool keepfiles)
    : _keepFiles(keepfiles),
    _refCount(1),
    _bound(0), 
    _exceptionCode(0), 
    _score(0),
    _filePath(firstInputPath), 
    _pFather(nullptr)    // pas de père pour la première entrée
{
    std::string::size_type pos = std::string(firstInputPath).find_last_of("\\/");
    this->_fileName = firstInputPath.substr(pos + 1); // antislash exclus 
}

// création du 'nb' nouvel objet dérivé de l'objet 'pFather' à la contrainte 'b'
CInput::CInput(CInput* pFather, UINT64 nb, UINT32 b) 
    : _keepFiles(pFather->_keepFiles),
    _refCount(1),  // sachant qu'à 0 il est detruit
    _bound(b), 
    _exceptionCode(0),
    _pFather(pFather),
    _score(0),
    _fileName("input" + std::to_string((_Longlong) nb))
{ 	
    // construction du chemin de fichier à partir de celui du père
    std::string fatherFilePath = pFather->getFilePath();
    std::string::size_type pos = fatherFilePath.rfind(pFather->getFileName());
    this->_filePath = fatherFilePath.substr(0, pos) + this->_fileName;

    // nouvel enfant : augmentation du refCount du père (qui existe forcément)
    this->_pFather->incRefCount();
}

CInput::~CInput()
{    
    // effacement du fichier, si l'option 'keepfiles' n'est pas spécifiée
    // ET que l'entrée n'a pas provoquée de fautes
    if (!_keepFiles && !_exceptionCode)  remove(this->_filePath.c_str());
}

// Accesseurs renvoyant les membres privés de la classe
CInput* CInput::getFather() const { return _pFather; }
UINT32  CInput::getBound() const  { return _bound; }
UINT32  CInput::getScore() const  { return _score; }
UINT32  CInput::getExceptionCode() const       { return _exceptionCode; }
const std::string& CInput::getFilePath() const { return _filePath; }
const std::string& CInput::getFileName() const { return _fileName; }

// numéro de contrainte inversée qui a donné naissance à cette entrée
void CInput::setBound(const UINT32 b)	{ _bound = b; }
// Affectation d'un score à cette entrée
void CInput::setScore(const UINT32 s)	{ _score = s; }
// numéro d'Exception généré par cette entrée
void CInput::setExceptionCode(const UINT32 e)	{ _exceptionCode = e; }

// gestion de la vie des objets "CInput" : refCount basique
void   CInput::incRefCount()       { _refCount++; }
UINT32 CInput::decRefCount()       { return (--_refCount); }
UINT32 CInput::getRefCount() const { return (_refCount); }

// renvoie la taille de l'entrée en octets
UINT32 CInput::getFileSize() const
{
    std::ifstream in(_filePath.c_str(), std::ifstream::in | std::ifstream::binary);
    in.seekg(0, std::ifstream::end);
    UINT32 length = static_cast<UINT32>(in.tellg()); 
    in.close();
    return (length);
}

// renvoie le chemin vers le fichier qui contiendra la formule SMT2
// associée à l'execution de cette entrée (option --keepfiles mise à TRUE)
std::string CInput::getLogFile() const { return (_filePath + ".fzw"); }

// renvoie le contenu du fichier sous la forme de string
std::string CInput::getFileContent() const
{
    UINT32 fileSize = this->getFileSize(); // UINT32 => fichier < 2Go...
    std::vector<char> contentWithChars(fileSize);

    // ouverture en mode binaire, lecture et retour des données
    std::ifstream is (_filePath.c_str(), std::ifstream::binary);
    is.read(&contentWithChars[0], fileSize);

    return (std::string(contentWithChars.begin(), contentWithChars.end()));    
}

// fonction de tri de la liste d'entrées de tests
bool sortCInputs(CInput* pA, CInput* pB) 
{ 
    return (pA->getScore() < pB->getScore()); 
}

/*********************/
/* FUZZWIN_ALGORITHM */
/*********************/

FuzzwinAlgorithm::FuzzwinAlgorithm(OSTYPE osType)
    : _osType(osType), 
      _hZ3_process (nullptr), _hZ3_stdin(nullptr),  _hZ3_stdout(nullptr),   _hZ3_thread(nullptr),
      _hReadFromZ3 (nullptr), _hWriteToZ3(nullptr), _hPintoolPipe(nullptr), _hTimer(nullptr),
      _regexModel(parseZ3ResultRegex, std::regex::ECMAScript),
      _nbFautes(0), _numberOfChilds(0) {}

FuzzwinAlgorithm::~FuzzwinAlgorithm()
{
    // fermeture du processus Z3
    CloseHandle(_hZ3_process); CloseHandle(_hZ3_thread);
    // fermeture des différents tubes de communication avec Z3
    CloseHandle(_hZ3_stdout); 	CloseHandle(_hZ3_stdin);
    CloseHandle(_hReadFromZ3);	CloseHandle(_hWriteToZ3);
    // fermeture des tubes nommés avec le pintool Fuzzwin
    CloseHandle(_hPintoolPipe);
    // fermeture handle du timer
    if (_maxExecutionTime) CloseHandle(this->_hTimer);
}

/************************/
/**  ALGORITHME SEARCH **/
/************************/

// cette fonction entretient une liste de fichiers d'entrée et 
// procède aux tests de ces entrées. 
// La fonction retourne le nombre de fichiers qui provoquent une faute
// dans le programme étudié

// TODO : trier la liste à chaque fois que de nouveaux fichiers sont générés, 
// afin d'exécuter en priorité les fichiers ayant une couverture de code maximale
// nécessite l'implémentation d'une fonction de "scoring"

void FuzzwinAlgorithm::algorithmSearch() 
{
    // calcul du hash de la première entrée, et insertion dans la liste des hashes
    // seulement si l'option est présente
    if (_hashFiles)
    {
        _hashTable.insert(calculateHash(
            _pCurrentInput->getFileContent().c_str(), 
            _pCurrentInput->getFileContent().size()));
    }

    // initialisation de la liste de travail avec la première entrée
    _workList.push_back(_pCurrentInput);

    /**********************/
    /** BOUCLE PRINCIPALE */
    /**********************/
    while ( !_workList.empty() ) 
    {
        this->logTimeStamp();
        this->log(std::to_string(_workList.size()) + " élément(s) dans la liste de travail");
        this->logEndOfLine();

        // tri des entrées selon leur score (si option activée)
        if (_computeScore) _workList.sort(sortCInputs);

        // récupération et retrait du fichier ayant le meilleur score (dernier de la liste)
        _pCurrentInput = _workList.back();
        _workList.pop_back();

        this->logTimeStamp();
        this->log("  exécution de " + _pCurrentInput->getFileName());
        
        this->logVerbose(" (bound = " + std::to_string(_pCurrentInput->getBound()) + ')');
        if (_computeScore)
        {
            this->logVerbose(" (score = " + std::to_string(_pCurrentInput->getScore()) + ')');
        }
        if (_pCurrentInput->getFather()) 
        {
            this->logVerbose(" (père = " + _pCurrentInput->getFather()->getFileName() + ')');
        }

        this->logEndOfLine();

        // exécution de PIN avec cette entrée (fonction ExpandExecution)
        // et recupération d'une liste de fichiers dérivés
        // la table de hachage permet d'écarter les doublons déjà générés
        ListOfInputs childInputs = expandExecution();

        this->logTimeStamp();

        if (!childInputs.size())  this->log("  pas de nouveaux fichiers");  
        else  this->log("  " + std::to_string(childInputs.size()) + " nouveau(x) fichier(s)");

        this->logEndOfLine();

        // insertion des fichiers dans la liste, et diminution du 
        // refcount de l'objet venant d'être testé
        _workList.insert(_workList.cbegin(), childInputs.cbegin(), childInputs.cend());
        // mise à jour des refcount des ancêtres, avec destruiction si nécessaire
        this->updateRefCounts(_pCurrentInput);
    }
}

void FuzzwinAlgorithm::updateRefCounts(CInput *pInput) const
{
    // fonction récursive de diminution des refcount
    // cela pourrait être géré directement dans le destructeur de la classe CInput
    // mais il serait impossible de logger les detructions d'objets

    // si refcount de l'objet à 0, diminuer celui du père avant destruction
    if (pInput->decRefCount() == 0)
    {
        CInput *pFather = pInput->getFather();

        this->logVerboseTimeStamp();
        this->logVerbose("    destruction objet " + pInput->getFileName());
        this->logVerboseEndOfLine();
  
        // si un ancêtre existe : diminution de son RefCount (recursivité)
        if (pFather) this->updateRefCounts(pFather);

        // destruction de l'objet actuel
        delete (pInput);
    }
}

/*********************************/
/**  ALGORITHME EXPANDEXECUTION **/
/*********************************/

// cette fonction génère de nouveaux fichiers d'entrée à partir d'une entrée fournie
// 1) exécution du premier PINTOOL ("FuzzWin") retournant une formule SMT2 brute
// 2) récupération du nombre de contraintes dans ce fichier
// 3) pour j dans [bound + 1, nbContraintes] :
//		inverser la contrainte numéro J et envoyer la formule au solveur
//		si une solution existe :  
//			génération d'un nouveau fichier avec les octets modifiés
//			calcul du hash, si déjà présent ne pas retenir la solution
//			atribution du "bound" = j à ce nouveau fichier
//			ajout du fichier à la liste des fichiers générés
//	 (fin de la boucle j)
// retour de la liste des fichiers ainsi générés

UINT32 FuzzwinAlgorithm::sendNonInvertedConstraints(UINT32 bound)
{
    if (bound) 
    {
        UINT32 posBeginOfLine = 0; // position du début de ligne de la contrainte 'bound'
        UINT32 posEndOfLine   = 0; // position du fin de ligne de la contrainte 'bound'
    
        // recherche de la contrainte "bound" dans la formule
        posBeginOfLine	= _formula.find("(assert (= C_" + std::to_string((_Longlong) bound));
        // recherche de la fin de la ligne
        posEndOfLine	= _formula.find_first_of('\n', posBeginOfLine);
        // extraction des contraintes non inversées et envoi au solveur
        sendToSolver(_formula.substr(0, posEndOfLine + 1));
        return (posEndOfLine); // position de la fin de la dernière contrainte dans la formule
    }
    else return (0);
}

// renvoie l'inverse de la contrainte fournie en argument
// la contrainte originale (argument fourni) reste inchangée
std::string FuzzwinAlgorithm::invertConstraint(const std::string &constraint) 
{
    // copie de la contrainte
    std::string invertedConstraint(constraint);
    UINT32 pos = invertedConstraint.find("true");
    
    if (pos != std::string::npos)  // 'true'  -> 'false' 
    {
        invertedConstraint.replace(pos, 4, "false");   
    }
    else  // 'false' -> 'true'
    {
        invertedConstraint.replace(invertedConstraint.find("false"), 5, "true");  
    }
    return (invertedConstraint);
}

ListOfInputs FuzzwinAlgorithm::expandExecution() 
{  
    ListOfInputs result;	                          // liste de nouveaux objets de type CInput générées
    UINT32	     bound = _pCurrentInput->getBound();  // bound du fichier actuellement étudié
    UINT32       pos = 0;
    UINT32       posLastConstraint = 0;  // indexs de position dans une chaine de caractères
    
    std::string  inputContent;         // contenu du fichier étudié
    std::string	 constraintJ;	       // partie de formule associée à la contrainte J
    std::string  constraintJ_inverted; // la même contrainte, inversée

    /********************************************************/
    /** Execution du pintool et récupération de la formule **/
    /********************************************************/
    this->callPintool();

    if (_formula.empty())
    {
        this->logTimeStamp();
        this->log("  !! Aucune formule recue du pintool !!");
        this->logEndOfLine();
        return (result); // aucune formule ou erreur
    }

    // récupération du nombre de contraintes dans la formule
    pos = _formula.find_last_of('@');
    if (std::string::npos == pos) return result;
    UINT32 nbContraintes = std::stoi(_formula.substr(pos + 1));

    this->logTimeStamp();
    this->log("  " + _formula.substr(pos + 1) + " contraintes extraites");
    this->logEndOfLine();

    // si le "bound" est supérieur aux nombre de contraintes => aucune nouvelle entrée, retour
    if (bound >= nbContraintes) 	
    {
        this->logTimeStamp();
        this->logVerbose("    Pas de nouvelles contraintes inversibles");
        this->logVerboseEndOfLine();
        return (result);
    }
    
    /********************************************/
    /** Traitement et résolution de la formule **/
    /********************************************/

    // les contraintes de 0 à bound ne seront pas inversées => les envoyer au solveur
    // en retour, un index pointant vers la fin de la dernière contrainte envoyée
    posLastConstraint = sendNonInvertedConstraints(bound);
    
    // récupération du contenu du fichier cible étudié
    inputContent = _pCurrentInput->getFileContent(); 

    // => boucle sur les contraintes de "bound + 1" à "nbContraintes" inversées et resolues successivement
    for (UINT32 j = bound + 1 ; j <= nbContraintes ; ++j) 
    {	
        this->logVerboseTimeStamp();
        this->logVerbose("    inversion contrainte " + std::to_string(j));
            
        // recherche de la prochaine contrainte dans la formule, à partir de la position de la précédente contrainte 
        pos = _formula.find("(assert (=", posLastConstraint);          
        // envoi au solveur de toutes les déclarations avant la contrainte
        this->sendToSolver(_formula.substr(posLastConstraint, (pos - posLastConstraint)));
        // envoi au solveur de la commande "push 1"
        // reserve une place sur la pile pour la prochaine déclaration (la contrainte inversée)
        this->sendToSolver("(push 1)\n");

        // recherche de la fin de la ligne de la contrainte actuelle (et future précédente contrainte)
        posLastConstraint    = _formula.find_first_of('\n', pos);     
        // extraction de la contrainte, et inversion
        constraintJ          = _formula.substr(pos, (posLastConstraint - pos));
        constraintJ_inverted = invertConstraint(constraintJ);    

        // envoi de la contrainte J inversée au solveur, et recherche de la solution
        this->sendToSolver(constraintJ_inverted + '\n');

        if (this->checkSatFromSolver())	// SOLUTION TROUVEE : DEMANDER LES RESULTATS
        {							
            std::string newInputContent(inputContent); // copie du contenu du fichier initial
            std::string solutions;

            // récupération des solutions du solveur
            solutions = getModelFromSolver();
                
            // modification des octets concernés dans le contenu du nouveau fichier
            int tokens[2] = {1, 2};
            std::sregex_token_iterator it (solutions.begin(), solutions.end(), _regexModel, tokens);
            std::sregex_token_iterator end;
            while (it != end) 
            {
                int offset = std::stoi(it->str(), nullptr, 10); ++it; // 1ere valeur = offset
                int value =  std::stoi(it->str(), nullptr, 16); ++it; // 2eme valeur = valeur
                newInputContent[offset] = static_cast<char>(value);
            }

            // calcul du hash du nouveau contenu et insertion dans la table de hachage. 
            // seulement si option présente
            // Si duplicat (retour 'false'), ne pas créer le fichier
            
            bool createNewInput = true;  // par défaut on créé la nouvelle entrée

            if (_hashFiles)
            {
                auto insertResult = _hashTable.insert(
                    calculateHash(newInputContent.c_str(), newInputContent.size()));
                
                if (insertResult.second == false) // le hash est présent : le fichier existe déjà !!
                {
                    this->logVerbose(" -> deja généré !!");
                    this->logVerboseEndOfLine();
                    createNewInput = false;
                }
            }

            if (createNewInput)
            {
                // fabrication du nouvel objet "fils" à partir du père
                CInput *newChild = new CInput(_pCurrentInput, ++_numberOfChilds, j);

                // création du fichier et insertion du contenu modifié
                std::ofstream newFile(newChild->getFilePath(), std::ios::binary);
                newFile.write(newInputContent.c_str(), newInputContent.size());
                newFile.close();

                this->logVerbose(" -> nouveau fichier " + newChild->getFileName());

                // test du fichier de suite; si retour nul le fichier est valide, donc l'insérer dans la liste
                UINT32 checkError = this->debugTarget(newChild);
                if (!checkError) result.push_back(newChild);
                else ++_nbFautes;
            }	     
        }
        // pas de solution trouvée par le solveur
        else 
        {
            this->logVerbose(" : aucune solution");
            this->logVerboseEndOfLine();
        }
       
        // enlever la contrainte inversée de la pile du solveur, et remettre l'originale
        this->sendToSolver("(pop 1)\n" + constraintJ + '\n');
    } // end for
       
    // effacement de toutes les formules pour laisser une pile vierge
    // pour le prochain fichier d'entrée qui sera testé
    this->sendToSolver("(reset)\n");

    return (result);
}

UINT32 FuzzwinAlgorithm::getNumberOfFaults() const { return _nbFautes; }

void FuzzwinAlgorithm::start() { this->algorithmSearch(); }