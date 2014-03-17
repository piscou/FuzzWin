#pragma once
#include <QtCore/QThread>
#include <QtCore/QFileInfo>
#include <QtCore/QTextStream>
#include <QtWidgets/QTreeWidgetItem>
#include <QtCore/QSet>
#include <QtCore/QDir>
#include <QtCore/QList>
#include <QtCore/QCryptographicHash>
#include <QtCore/QTimer>


#include <process.h>
#include <cstdint>  // uint8_t etc...	
#include <regex>

#include "utilities.hpp" // getKindOfExe, OS_TYPE, getNativeArchitecture, commun avec la ligne de commande


class CInput;
class FuzzwinAlgorithm;

typedef QList<CInput*>          ListOfInputs;
typedef QSet<QByteArray>        HashTable;

/* solutions fournies par le solveur sont du type
   define OFF?? (_BitVec 8) 
      #x??    */ 
#define parseZ3ResultRegex "OFF(\\d+).*\r\n.*([0-9a-f]{2})"

static inline QString toQString(const std::string &qstr)
{
    return (QString::fromLocal8Bit(qstr.c_str()));
}

class CInput : public QTreeWidgetItem
{
private:
    quint32	  _bound;	      // numéro de contrainte inversée qui a mené à la création du fichier
    quint32	  _exceptionCode; // code d'erreur engendré par le fichier. 0 si aucun
    QFileInfo _fileInfo;      // chemin vers le fichier
    quint32    _score;        // score de l'entrée (couverture de code)

public:
    // création du 'nb' nouvel objet dérivé de l'objet 'pFather' à la contrainte 'b'
    CInput(CInput* pFather, quint32 nb, quint32 b);
    // constructeur spécifique 1ere entrée
    CInput(const QString &firstInputPath);

    ~CInput();

    quint32	  getBound() const;  
    quint32	  getScore() const; 
    quint32	  getExceptionCode() const;
    quint32   getFileSize() const;
    QFileInfo getFileInfo() const;

    std::string getFilePath() const;
    QString     getLogFilePath() const; 
    std::string getFileContent() const;
    
    void setBound(const quint32 b);
    void setScore(const quint32 s);
    void setExceptionCode(const quint32 e);
};

inline bool sortCInputs(CInput* pA, CInput* pB) { return (pA->getScore() < pB->getScore()); }

class FuzzwinAlgorithm : public QObject
{
    Q_OBJECT

public: // initialisation à la construction du thread, et récup du nombre de fautes à la fin

    QString     _resultDir;         // dossier de résultats
    QString     _faultFile;         // fichier texte retracant les fautes trouvées
    std::string _targetPath;        // exécutable fuzzé
    std::string _bytesToTaint;      // intervalles d'octets à surveiller
    std::string _z3Path;            // chemin vers le solveur Z3

    std::string _formula;           // formule retournée par le pintool

    std::string _cmdLinePin;	    // ligne de commande du pintool, pré-rédigée
    quint32     _nbFautes;          // nombre de fautes trouvées au cours de l'analyse

    bool    _keepFiles;         // les fichiers sont gardés dans le dossier de resultat
    bool    _computeScore;      // option pour calculer le score de chaque entrée
    bool    _verbose;           // mode verbeux
    
    quint32  _maxExecutionTime;  // temps maximal d'execution 
    quint32  _maxConstraints;    // nombre maximal de contraintes à récupérer

    OSTYPE _osType;             // type d'OS natif

private:
    HANDLE _hZ3_process;	// handle du process Z3
    HANDLE _hZ3_thread;	// handle du thread Z3
    HANDLE _hZ3_stdout;	// handle du pipe correspondant à la sortie de Z3(= son stdout)
    HANDLE _hZ3_stdin;	// handle du pipe correspondant à l'entrée de Z3 (= son stdin)
    HANDLE _hReadFromZ3;	// handle pour lire les résultats de Z3
    HANDLE _hWriteToZ3;	// handle pour envoyer des données vers Z3
    HANDLE _hPintoolPipe; // handle du named pipe avec le pintool Fuzzwin
    HANDLE _hDebugProcess;   // handle du programme en cours de déboggage

    quint32    _numberOfChilds;	// numérotation des fichiers dérivés
    
    HashTable          _hashTable;
    QCryptographicHash _hash;

    QTimer *_pOutOfTimeDebug;

    CInput          *_currentInput; // entrée en cours de test
    const std::regex _regexModel; // pour parser les resultats du solveur

// méthodes privées 
    quint32      sendNonInvertedConstraints(quint32 bound);
    std::string  invertConstraint(const std::string &constraint);
    ListOfInputs expandExecution();
 
    DWORD        debugTarget(CInput *newInput);
    int          sendArgumentsToPintool(const std::string &command);
    void         callFuzzwin();
    bool         sendToSolver(const std::string &data);
    bool         checkSatFromSolver();
    std::string  getModelFromSolver();
    bool         createSolverProcess(const std::string &solverPath);
    int          createNamedPipePintool();
    // renvoie la ligne de commande complète pour l'appel du pintool avec l'entrée actuelle
    std::string  getCmdLineFuzzwin() const;
    // renvoie la ligne de commande complète pour l'execution de la cible en mode debug
    std::string  getCmdLineDebug(const CInput *pInput) const;

signals:
    void sendToGui(const QString &msg);
    void sendToGuiVerbose(const QString &msg);
    void newInput(CInput);

public slots:
    void    outOfTimeDebug(); // fonction appelée en cas de dépassement du temps maximal
    void    algorithmSearch(); // démarrage de l'algo
public:
    explicit FuzzwinAlgorithm(const QString &firstInputPath, const QString &targetPath, const QString &resultsDir);  
    ~FuzzwinAlgorithm();

    void buildPinCmdLine(const QString &pin_X86,     const QString &pin_X64, 
                         const QString &pintool_X86, const QString &pintool_X64);

};
