#pragma once

#include <string>   
#include <regex>
#include <list>
#include <set>
#include <fstream>

#include <windows.h>

#include "md5.h" // hash des fichiers, résultat en b64
#include "osType.h"

/* solutions fournies par le solveur sont du type
define OFF?? (_BitVec 8) 
#x??    */ 
#ifndef parseZ3ResultRegex
#define parseZ3ResultRegex "OFF(\\d+).*\r\n.*([0-9a-f]{2})"
#endif

class   CInput;
class   FuzzwinAlgorithm;

typedef std::list<CInput*>    ListOfInputs;
typedef unsigned char         UINT8;
typedef unsigned int          UINT32;
typedef unsigned long long    UINT64;
typedef std::set<std::string> HashTable; // stockage des hashes (MD5 base64) des fichiers déjà générés

static const std::string solverConfig
    (
    "(set-option :auto-config false)"   \
    "(set-option :produce-models true)" \
    "(set-option :print-success false)" \
    "(set-option :relevancy 0)"         \
    "(set-option :smtlib2_compliant true)"  \
    "(set-logic QF_AUFBV)"
    );

static const std::string infoHeader
    (   
    "; **************************************************\n" 
    "; *  FUZZWIN : FUZZER AUTOMATIQUE SOUS WINDOWS     *\n" 
    "; *  v1.3 (c) Sebastien LECOMTE 26/03/2014         *\n"
    "; *  PIN Version 2.13 kit 62732 et Z3 version 4.3  *\n"
    "; **************************************************\n" 
    );

// test du type d'exécutable (32 ou 64bits). Si non supporté => retour négatif (-1)
int getKindOfExecutable(const std::string &targetPath);

// chemin complet d'un fichier (sans référence au dossier de travail)
std::string getAbsoluteFilePath(const std::string &s);

// détermination du type l'OS dynamiquement, inspiré de l'exemple fourni sur MSDN
OSTYPE getNativeArchitecture();

/*********************************************/
/* ALGORITHME (DERIVEES DANS CMDLINE ET GUI) */
/*********************************************/

class CInput
{
private:
    UINT32 _refCount;      // implémentation "basique" d'un sharedPtr
    UINT32 _bound;         // numéro de contrainte inversée qui a mené à la création du fichier
    UINT32 _exceptionCode; // code d'erreur engendré par le fichier. 0 si aucun
    UINT32 _score;         // score de l'entrée (couverture de code)
    std::string  _filePath;   // chemin vers le fichier
    std::string  _fileName;   // nom de fichier uniquement (sans le chemin)
    CInput*      _pFather;    // entrée de laquelle cette entrée est dérivée
    
public:
    // constructeur spécifique 1ere entrée
    CInput(const std::string &firstInputPath, bool keepfiles);
    // création du 'nb' nouvel objet dérivé de l'objet 'pFather' à la contrainte 'b'
    CInput(CInput* pFather, UINT64 nb, UINT32 b); 

    ~CInput() ;

    const bool   _keepFiles;  // si VRAI, en pas effacer physiquement le fichier à la destruction 

    CInput* getFather() const;

    // Accesseurs renvoyant les membres privés de la classe
    UINT32 getBound() const;
    UINT32 getScore() const;
    UINT32 getExceptionCode() const;
    const std::string& getFilePath() const;
    const std::string& getFileName() const;

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
}; // class CInput_common

// fonction de tri de la liste d'entrées de tests
bool sortCInputs(CInput* pA, CInput* pB);

class FuzzwinAlgorithm
{
protected:
    OSTYPE   _osType;   // type d'OS natif

    const std::regex   _regexModel;     // pour parser les resultats du solveur

    std::string  _resultsDir;     // dossier de résultats
    std::string  _targetPath;     // exécutable fuzzé
    std::string  _bytesToTaint;   // intervalles d'octets à surveiller 
    std::string  _z3Path;         // chemin vers le solveur Z3

    std::string  _cmdLinePin;   // ligne de commande du pintool, pré-rédigée
    std::string  _faultFile;    // fichier texte retracant les fautes trouvées
    std::string  _formula;      // formule retournée par le pintool

    UINT32 _nbFautes;          // nombre de fautes trouvées au cours de l'analyse
    UINT32 _maxExecutionTime;  // temps maximal d'execution 
    UINT32 _maxConstraints;    // nombre maximal de contraintes à récupérer

    bool   _keepFiles;         // les fichiers sont gardés dans le dossier de resultat
    bool   _computeScore;      // option pour calculer le score de chaque entrée
    bool   _verbose;           // mode verbeux
    bool   _timeStamp;         // ajout de l'heure aux lignes de log
    bool   _hashFiles;         // calcul du hash de chaque entrée pour éviter les collisions

    HANDLE  _hZ3_process;  // handle du process Z3
    HANDLE  _hZ3_thread;   // handle du thread Z3
    HANDLE  _hZ3_stdout;   // handle du pipe correspondant à la sortie de Z3(= son stdout)
    HANDLE  _hZ3_stdin;    // handle du pipe correspondant à l'entrée de Z3 (= son stdin)
    HANDLE  _hReadFromZ3;  // handle pour lire les résultats de Z3
    HANDLE  _hWriteToZ3;   // handle pour envoyer des données vers Z3
    HANDLE  _hPintoolPipe; // handle du named pipe avec le pintool Fuzzwin
    HANDLE  _hTimer;       // handle du timer (temps maximal d'exécution)

    ListOfInputs _workList;       // liste des fichiers à traiter 
    UINT32       _numberOfChilds; // numérotation des fichiers dérivés
    CInput*      _pCurrentInput;  // entrée en cours de test
    
    HashTable    _hashTable;      // table de hachage des fichiers déjà traités

    
    /*** METHODES PRIVEES (PROTECTED) ***/
    
    /* redefinition de la sortie des resultats dans les classes dérivées */

    virtual void log(const std::string &msg)        const = 0;
    virtual void logEndOfLine()                     const = 0;
    virtual void logTimeStamp()                     const = 0;

    virtual void logVerbose(const std::string &msg) const = 0;
    virtual void logVerboseEndOfLine()              const = 0;
    virtual void logVerboseTimeStamp()              const = 0;

    /* partie algorithme pur (fuzzwin_algo.cpp) */
    void         algorithmSearch();  
    ListOfInputs expandExecution(); 
    UINT32       sendNonInvertedConstraints(UINT32 bound);
    std::string  invertConstraint(const std::string &constraint);
    void         updateRefCounts(CInput *pInput) const;   

    /* PARTIE Communication avec pintool (pintool_interface.cpp)*/

    int          sendArgumentToPintool(const std::string &argument) const;
    void         callPintool();
    int          createNamedPipePintool();
    std::string  getCmdLinePintool() const;

    /* PARTIE Communication avec solveur (solver_interface.cpp) */

    bool         createSolverProcess(const std::string &solverPath);    
    bool         sendToSolver(const std::string &data) const;
    bool         checkSatFromSolver() const;
    std::string  getModelFromSolver() const;

    /* PARTIE deboggage du programme (debug_interface.cpp) */
    
    DWORD        debugTarget(CInput *pNewInput);        
    std::string  getCmdLineDebug(const CInput *pNewInput) const;
    static void  CALLBACK timerExpired(LPVOID arg, DWORD, DWORD);

public:

    explicit FuzzwinAlgorithm(OSTYPE osType);
    ~FuzzwinAlgorithm();
    void    start();
    UINT32  getNumberOfFaults() const;
};