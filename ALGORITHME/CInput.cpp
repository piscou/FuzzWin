#include "CInput.h"

/*********************************************/
/* CINPUT : description d'une entrée de test */
/*********************************************/

CInput::CInput(const std::string &firstInputPath, bool keepfiles)
    : _keepFiles(keepfiles),
    _refCount(1),
    _bound(0), 
    _exceptionCode(0), 
    _score(0),
    _filePath(firstInputPath), // move semantics
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
UINT32  CInput::getExceptionCode() const { return _exceptionCode; }
std::string CInput::getFilePath() const  { return _filePath; }
std::string CInput::getFileName() const  { return _fileName; }

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
std::string CInput::getLogFile() const { return (_filePath + ".smt2"); }

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