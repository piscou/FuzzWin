#ifndef FUZZWIN_GUI_H
#define FUZZWIN_GUI_H

#include <QtCore/QVariant>
#include <QtCore/QProcess>

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
#include <QtWidgets/QLineEdit>
#include <QtWidgets/QMainWindow>
#include <QtWidgets/QMenu>
#include <QtWidgets/QMenuBar>
#include <QtWidgets/QPushButton>
#include <QtWidgets/QSpinBox>
#include <QtWidgets/QTabWidget>
#include <QtWidgets/QTextEdit>
#include <QtWidgets/QTimeEdit>
#include <QtWidgets/QTreeWidget>
#include <QtWidgets/QVBoxLayout>
#include <QtWidgets/QWidget>
#include <QtWidgets/QMainWindow>
#include <QtGui/QDragEnterEvent>
#include <QtGui/QDropEvent>
#include <QtCore/QMimeData>
#include <QtCore/QUrl>
#include <QtCore/QFile>

#include <QtWidgets/QFileDialog>
#include <QtWidgets/QMessageBox>


static inline std::string convertToString(const QString &qstr)
{
    return (std::string(qstr.toLocal8Bit().constData()));
}

// Bouton de selection personnalisé
class FuzzwinButton : public QPushButton
{
    Q_OBJECT

private:
    // booléen pour tester l'état du bouton (donnée ok ou non)
    bool _buttonStatus;

public:
    FuzzwinButton(QWidget *parent, const QString &text);
    ~FuzzwinButton();

    // bouton OK => couleur verte
    void setButtonOk();
    // bouton NON_ => couleur rougeatre
    void setButtonError();
    // status du bouton
    bool getStatus() const;
};

// lignes de textes personnalisées pour accepter le "drag & drop"
// seul le drag est commun, le drop dépend du type de ligne
class FuzzwinLineEdit : public QLineEdit
{
    Q_OBJECT

public:
    FuzzwinLineEdit(QWidget *parent);
protected:
    void dragEnterEvent(QDragEnterEvent *event);
};

class InitialInputLineEdit : public FuzzwinLineEdit
{
    Q_OBJECT

public:
    InitialInputLineEdit(QWidget *parent);
protected:
    void dropEvent(QDropEvent *event);
};

class TargetPathLineEdit : public FuzzwinLineEdit
{
    Q_OBJECT

public:
    TargetPathLineEdit(QWidget *parent);
    bool check(const QString &path);

protected:
    void dropEvent(QDropEvent *event);
};

class ResultsDirLineEdit : public FuzzwinLineEdit
{
    Q_OBJECT

public:
    ResultsDirLineEdit(QWidget *parent);
    // 0 => abandon, 1 => erreur, 2 => ok
    int check(const QString &dirPath);

protected:
    void dropEvent(QDropEvent *event);
};

class FUZZWIN_GUI : public QMainWindow
{
    Q_OBJECT

public:
    friend class InitialInputLineEdit;
    friend class TargetPathLineEdit;
    friend class ResultsDirLineEdit;
    
    FUZZWIN_GUI();
    ~FUZZWIN_GUI();

    void initialize();  // état des boutons au démarrage
    void sendToLogWindow(const QString &msg);

private:
    // chemin des exécutables PIN et Z3
    QString _pinPath_X86, _pinPath_X64;
    QString _pintool_X86, _pintool_X64;
    QString _z3Path;

    
    // taille des widgets
    QSizePolicy _fixedSizePolicy;

    // menu
    QMenuBar *_menuBar;
        QMenu    *_menuFichier;
        QAction  *_action_Quitter;
        QMenu    *_menuAbout;
        QAction  *_action_AboutFuzzWin;
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
    QPushButton *_saveSessionButton;
    QPushButton *_saveConfigButton;
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
            QTreeWidget *_listOfInputs;

    QProcessEnvironment _env;    // variables d'environnement du processus   

    bool _isZ3Launched;

    bool checkPinPath(QString &path);
    
    // initialisation des différents groupes d'objets. 
    // Fonctions appelées par le constructeur
    void initMenuBar();
    void initGroupConfiguration();
    void initGroupSession();
    void initGroupOptions();
    void initGroupResultats();
    void initButtons();
    void initLines();

    // réimplémentation de l'évènement "Close" pour demander confirmation
    void closeEvent(QCloseEvent *e);

public slots:
    void selectPin_clicked(); // selection du répertoire de PIN
    void selectZ3_clicked(); // sélection du répertoire de Z3
    void selectInitialInput_clicked(); // sélection de l'entrée initiale
    void selectTarget_clicked();       // sélection du programme cible
    void selectResultsDir_clicked();   // sélection du répertoire de résultats
    void quitFuzzwin();

    void go_clicked();

    void testGoButton();
};

extern FUZZWIN_GUI *w;

#endif // FUZZWIN_GUI_H
