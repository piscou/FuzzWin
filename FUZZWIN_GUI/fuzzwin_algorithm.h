#pragma once
#include <QtCore/QObject>
#include <QtCore/QFileInfo>
#include <QtWidgets/QTreeWidgetItem>
#include "fuzzwin.h"

class CInput;
class FuzzwinAlgorithm;

typedef std::list<CInput*>  ListOfInputs;

class CInput : public QTreeWidgetItem
{
private:
    UINT32	  _bound;	     // numéro de contrainte inversée qui a mené à la création du fichier
    UINT32	  _exceptionCode; // code d'erreur engendré par le fichier. 0 si aucun
    QFileInfo _fileInfo;  // chemin vers le fichier
    UINT32    _score;     // score de l'entrée (couverture de code)

public:
    // création du 'nb' nouvel objet dérivé de l'objet 'pFather' à la contrainte 'b'
    CInput(CInput* pFather, UINT64 nb, UINT32 b) : QTreeWidgetItem(pFather),
        _bound(b), 
        _exceptionCode(0),
        _score(0)
    { 	
        // construction du chemin de fichier à partir de celui du père
        // nom du dossier + nouveau nom de fichier
        _fileInfo = pFather->getFileInfo().absolutePath() + QString("input%1").arg(nb);
    }

    // constructeur spécifique 1ere entrée
    CInput(const QString &firstInputPath) : QTreeWidgetItem(),
       _bound(0), 
       _exceptionCode(0), 
       _score(0),
       _fileInfo(firstInputPath)  {}

    ~CInput() 
    {   
        // effacement du fichier du disque si l'option est déactivée
        if (!pGlobals->keepFiles) QFile::remove(_fileInfo.filePath());
    }

    // Accesseurs renvoyant les membres privés de la classe
    UINT32	getBound() const         { return this->_bound; }
    UINT32	getScore() const         { return this->_score; }
    UINT32	getExceptionCode() const { return this->_exceptionCode; }
    QFileInfo getFileInfo() const 	 { return this->_fileInfo; }

    // numéro de contrainte inversée qui a donné naissance à cette entrée
    void setBound(const UINT32 b)	{ this->_bound = b; }
    // Affectation d'un score à cette entrée
    void setScore(const UINT32 s)	{ this->_score = s; }
    // numéro d'Exception généré par cette entrée
    void setExceptionCode(const UINT32 e)	{ this->_exceptionCode = e; }

    // renvoie la taille de l'entrée en octets
    UINT32 getFileSize() const
    {
        return static_cast<UINT32>(_fileInfo.size());
    }

    // renvoie le chemin vers le fichier qui contiendra la formule SMT2
    // associée à l'execution de cette entrée (option --keepfiles mise à TRUE)
    std::string getLogFile() const 
    {
        QString logFileName(_fileInfo.absoluteFilePath() + ".fzw");
        return (qPrintable(logFileName));
    }

    // renvoie le contenu du fichier sous la forme de string
    std::string getFileContent() const
    {
        QFile file(_fileInfo.absoluteFilePath());
        
        UINT32 fileSize = static_cast<UINT32>(file.size());

        file.open(QIODevice::ReadOnly);
        QByteArray content = file.read(file.size());

        return (std::string(content, content.size()));    
    }

    // renvoie la ligne de commande complète pour l'appel du pintool
    std::string getCmdLineFuzzwin() const
    {
        std::string filePath = qPrintable(_fileInfo.absoluteFilePath());
        return (pGlobals->cmdLinePin + '"' + filePath + '"'); 
    }

    // renvoie la ligne de commande complète pour l'execution de la cible en mode debug
    std::string getCmdLineDebug() const
    {
        std::string filePath = qPrintable(_fileInfo.absoluteFilePath());
        return ('"' + pGlobals->targetPath + "\" \"" + filePath + '"'); 
    }
};

inline bool sortInputs(CInput* pA, CInput* pB) { return (pA->getScore() < pB->getScore()); }



class FuzzwinAlgorithm : public QObject
{
    Q_OBJECT

private:
    UINT32 _numberOfChilds;	// numérotation des fichiers dérivés
    HANDLE _hTimoutEvent;
    HANDLE _hTimerThread;

    size_t       sendNonInvertedConstraints(const std::string &formula, UINT32 bound);
    std::string  invertConstraint(const std::string &constraint);
    ListOfInputs expandExecution(CInput *pInput, HashTable &h, UINT32 *nbFautes);
    UINT32       algorithmeSearch(); 
    DWORD        debugTarget(CInput *pInput);
    DWORD WINAPI timerThread(LPVOID lpParam);

signals:
    void sendToGui(const QString &msg);
    void sendToGuiVerbose(const QString &msg);
    
public:
    FuzzwinAlgorithm();
    void launch();

};
