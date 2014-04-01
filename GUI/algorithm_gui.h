#pragma once
#include <QtCore\QObject>
#include <QDateTime>

#include "../ALGORITHME/algorithm.h"

#define TIMESTAMP     QDateTime::currentDateTime().time().toString("[HH:mm:ss:zzz] ")
#define LINEFEED      QString("<br>")
#define TEXTRED(x)    QString("<font color=\"Red\">"##x##"</font>")
#define TEXTGREEN(x)  QString("<font color=\"Green\">"##x##"</font>")

class ArgumentsForAlgorithm // structure pour initialiser l'algo en mode GUI
{
public:
    /* donnnées de session */
    std::string _resultsDir;     // dossier de résultats
    std::string _firstInputPath; // première entrée testée
    std::string _targetPath;     // exécutable fuzzé
    
    /* outils externes */
    std::string _z3Path;     // chemin vers le solveur Z3
    std::string _cmdLinePin; // ligne de commande pré-remplie pour PIN

    /* Options pour le fuzzing */
    UINT32  _maxExecutionTime;  // temps maximal d'execution 
    UINT32  _maxConstraints;    // nombre maximal de contraintes à récupérer
    bool    _keepFiles;         // les fichiers sont gardés dans le dossier de resultat
    bool    _computeScore;      // option pour calculer le score de chaque entrée
    bool    _verbose;           // mode verbeux
    bool    _timeStamp;         // ajout de l'heure aux lignes de log
    bool    _hashFiles;         // calcul du hash de chaque entrée pour éviter les collisions
    bool    _traceOnly;         // simple trace d'exécution de l'entrée initiale
    std::string _bytesToTaint;      // intervalles d'octets à surveiller 
};

// création de la classe algorithme adapté à la ligne de commande

class FuzzwinAlgorithm_GUI : public QObject, public FuzzwinAlgorithm 
{    
    Q_OBJECT
public:
    FuzzwinAlgorithm_GUI(OSTYPE osType, ArgumentsForAlgorithm *pArgs);

private:
    /**  implémentation des méthodes virtuelles pures de log **/

    void log(const std::string &msg) const;        // envoi en console
    void logVerbose(const std::string &msg) const; // idem en mode verbose
    void logVerboseEndOfLine() const;
    void logEndOfLine() const;
    void logTimeStamp() const;
    void logVerboseTimeStamp() const;

signals: // signaux émis par l'algorithme vers la GUI
    void sendToGui(const QString&) const;
    void sendAlgorithmFinished();
    void sendTraceOnlyFinished();
    void pauseIsEffective();
    void setFaultsFound(int);

public slots:
    
    /*** implémentation des méthodes virtuelles pures de contrôle de l'algorithme ***/
    void algorithmFinished(); 
    void notifyAlgoIsPaused();
    void faultFound();
    void algorithmTraceOnlyFinished();

    // wrappers permettant d'appeler les méthodes de l'algorithme parent éponymes
    void wrapStartFromGui();
    void wrapStopFromGui();
    void wrapPauseFromGui();
};