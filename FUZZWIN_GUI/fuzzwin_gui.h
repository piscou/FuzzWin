#pragma once

#include <QtCore/QVariant>
#include <QtCore/QProcess>
#include <QtCore/QThread>
#include <QtCore/QTextStream>

#include <QtWidgets/QAction>
#include <QtWidgets/QApplication>
#include <QtWidgets/QButtonGroup>
#include <QtWidgets/QCheckBox>
#include <QtWidgets/QFrame>
#include <QtWidgets/QGridLayout>
#include <QtWidgets/QGroupBox>
#include <QtWidgets/QHBoxLayout>
#include <QtWidgets/QHeaderView>
#include <QtWidgets/QLabel>
#include <QtWidgets/QMainWindow>
#include <QtWidgets/QSpinBox>
#include <QtWidgets/QTabWidget>
#include <QtWidgets/QTextEdit>
#include <QtWidgets/QTimeEdit>
#include <QtWidgets/QTreeWidget>
#include <QtWidgets/QVBoxLayout>
#include <QtWidgets/QWidget>
#include <QtWidgets/QFileDialog>
#include <QtWidgets/QScrollBar>

#include <QtGui/QStandardItemModel>

//#include "fuzzwin_algorithm.h"  // classe fuzzwinThread
#include "fuzzwin_widgets.h"
#include "fuzzwin_modelview.h"
#include "qhexview.h"

#include "../FUZZWIN_COMMON/fuzzwin_algo.h"

#include <QDateTime>
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
    bool    _traceonly;         // simple trace d'exécution de l'entrée initiale
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
    void sendNbFautes(int);
    void pauseIsEffective();

public slots:
    
    /*** implémentation des méthodes virtuelles pures de contrôle de l'algorithme ***/
    void finishSpecific(); 
    void notifyAlgoIsPaused();

    // wrappers permettant d'appeler les méthodes de l'algorithme parent éponymes
    void wrapStartFromGui();
    void wrapStopFromGui();
    void wrapPauseFromGui();

};

class FUZZWIN_GUI : public QMainWindow
{
    Q_OBJECT

public:
    FUZZWIN_GUI();
    ~FUZZWIN_GUI();

    // test de la version de l'OS et de la présence du pintool
    // détermine également le marquage des boutons au démarrage
    int testConfig();  

private:
    /***** PARTIE NON_GUI *****/
    
    QProcessEnvironment   _env;            // variables d'environnement du processus  
    QThread              *_pFuzzwinThread; // thread de l'algo SAGE
    FuzzwinAlgorithm_GUI *_pFuzzwinAlgo;   // objet algorithme sage (lancé dans le thread supra)

    QString _pinPath_X86, _pinPath_X64;    // chemin des exécutables PIN  (32/64bits)
    QString _pintool_X86, _pintool_X64;    // chemin des DLL des pintools (32/64bits)
    QString _z3Path;                       // chemin vers Z3

    OSTYPE _osType;     // type d'OS Natif (version de Windows + archi 32/64)

    /***** PARTIE GUI *****/

    // status du bouton "Go" : soit Go, soit Pause, soit "Resume"
    enum STATUS_START_BUTTON
    {
        STATUS_START,
        STATUS_PAUSE,
        STATUS_RESUME
    };

    // taille des widgets
    QSizePolicy _fixedSizePolicy;

    // disposition globale
    QWidget     *_centralWidget;
    QGridLayout *_gCentralLayout;    
    QFrame      *_Vline;
    // Configuration : PIN et Z3
    QGroupBox     *_groupConfiguration;
    QHBoxLayout   *_hLayout1;
        FuzzwinButton *_selectPin;
        FuzzwinButton *_selectZ3;
    // Données concernant la session
    QGroupBox     *_groupSession;
    QVBoxLayout   *_vLayout1;
        FuzzwinButton *_selectInitialInput;
        FuzzwinButton *_selectTarget;
        FuzzwinButton *_selectResultsDir;
    // Options pour la session
    QGroupBox   *_groupOptions;
    QGridLayout *_gLayout1;
        QCheckBox   *_maxConstraintsEnabled;
        QSpinBox    *_maxConstraints;
        QCheckBox   *_maxTimeEnabled;
        QTimeEdit   *_maxTime;
        QCheckBox   *_bytesToTaintEnabled;
        QLineEdit   *_listOfBytesToTaint;
        QCheckBox   *_scoreEnabled;
        QCheckBox   *_verboseEnabled;
        QCheckBox   *_keepfilesEnabled;
        QCheckBox   *_traceOnlyEnabled;
    // boutons de commande
    QPushButton *_startButton;
    STATUS_START_BUTTON _startButtonStatus;
    QPushButton *_stopButton;
    QPushButton *_quitButton;
    QPushButton *_aboutButton;
    // partie résultats
    QGroupBox   *_groupResultats;
    QGridLayout *_gLayout2;
        QLabel      *_labelWorklistSize;
        QSpinBox    *_worklistSize;
        
        QLabel      *_labelElapsedTime;
        QLabel      *_labelInitialInput;
        InitialInputLineEdit   *_initialInput;    
        QLabel      *_labelTargetPath;
        TargetPathLineEdit   *_targetPath;
        QLabel      *_labelResultsDir;
        ResultsDirLineEdit   *_resultsDir;
        QTimeEdit   *_elapsedTime;
    // partie tabs
    QTabWidget  *_Tabs;
        QWidget     *_logTab;
        QHBoxLayout *_hLayout2;
        QTextEdit   *_logWindow;
        QWidget     *_entriesTab;
        QVBoxLayout *_vLayout2;
        QTreeView   *_inputsView;
        TreeModel   *_inputsModel;
    // boutons de sauvegarde
    QPushButton *_saveLogButton;
    QPushButton *_saveConfigButton;

    // initialisation des différents groupes d'objets et connection signal/slots
    // Fonctions appelées par le constructeur

    void initGroupConfiguration();
    void initGroupSession();
    void initGroupOptions();
    void initGroupResultats();
    void initButtons();
    void initLines();
    void connectSignalsToSlots();   

    // réimplémentation de l'évènement "Close" pour demander confirmation
    void closeEvent(QCloseEvent *e);    
 
signals:
    void launchAlgorithm();
    void pauseAlgorithm();
    void stopAlgorithm();

public slots:
    void selectPin_clicked(); // selection du répertoire de PIN
    void selectZ3_clicked(); // sélection du répertoire de Z3
    void selectInitialInput_clicked(); // sélection de l'entrée initiale
    void selectTarget_clicked();       // sélection du programme cible
    void selectResultsDir_clicked();   // sélection du répertoire de résultats
    void start_clicked();
    void stop_clicked();
    void saveLog_clicked(); 
    void saveConfig_clicked(); 
    void quitFuzzwin();
    
    void checkPinPath(QString path);  // vérification de l'intégrité du dossier racine de PIN
    void checkZ3Path(QString path);
    void checkKindOfExe(const QString &path); // vérification du type d'exécutable sélectionné
    void checkDir(const QString &path); // vérification du dossier de résultats (effacement si besoin)
     
    void log(const QString &msg);

    void startSession();
    void connectGUIToAlgo();
    void sessionPaused();

    void algoFinished(int nbFautes);
    void autoScrollLogWindow();

    void updateInputView(CInput input);
    void testButtons();
};
