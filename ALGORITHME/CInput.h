#pragma once
#include <list>
#include <vector>
#include <string>
#include <fstream>

typedef unsigned char         UINT8;
typedef unsigned int          UINT32;
typedef unsigned long long    UINT64;

class   CInput;
typedef std::list<CInput*>    ListOfInputs;

class CInput
{
private:
    UINT32       _refCount;      // implémentation "basique" d'un sharedPtr
    UINT32       _bound;         // numéro de contrainte inversée qui a mené à la création du fichier
    UINT32       _exceptionCode; // code d'erreur engendré par le fichier. 0 si aucun
    UINT32       _score;         // score de l'entrée (couverture de code)
    std::string  _filePath;      // chemin vers le fichier
    std::string  _fileName;      // nom de fichier uniquement (sans le chemin)
    CInput*      _pFather;       // entrée de laquelle cette entrée est dérivée
    
public:
    // constructeur spécifique 1ere entrée
    CInput(const std::string &firstInputPath, bool keepfiles);
    // création du 'nb' nouvel objet dérivé de l'objet 'pFather' à la contrainte 'b'
    CInput(CInput* pFather, UINT64 nb, UINT32 b); 

    // destructeur n'agit pas sur les ressources mais sur l'effacement du fichier
    // donc pas besoin d'appliquer la "rule of three"
    ~CInput();  
    const bool   _keepFiles;  // si VRAI, ne pas effacer physiquement le fichier à la destruction 

    CInput* getFather() const;

    // Accesseurs renvoyant les membres privés de la classe
    UINT32 getBound() const;
    UINT32 getScore() const;
    UINT32 getExceptionCode() const;
    std::string getFilePath() const;
    std::string getFileName() const;

    // numéro de contrainte inversée qui a donné naissance à cette entrée
    void setBound(const UINT32 b);
    // Affectation d'un score à cette entrée
    void setScore(const UINT32 s);
    // numéro d'Exception généré par cette entrée
    void setExceptionCode(const UINT32 e);

    // gestion de la vie des objets "CInput" : refCount basique
    void   incRefCount();
    UINT32 decRefCount();
    UINT32 getRefCount() const;

    // renvoie la taille de l'entrée en octets
    UINT32 getFileSize() const;

    // renvoie le chemin vers le fichier qui contiendra la formule SMT2
    // associée à l'execution de cette entrée (option --keepfiles mise à TRUE)
    std::string getLogFile() const;

    // renvoie le contenu du fichier sous la forme de string
    std::string getFileContent() const;
}; // class CInput

// fonction de tri de la liste d'entrées de tests
bool sortCInputs(CInput* pA, CInput* pB);