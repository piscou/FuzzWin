#ifndef FUZZWIN_GUI_H
#define FUZZWIN_GUI_H

#include <QtWidgets/QMainWindow>
#include <QtCore/QProcess>
#include "ui_fuzzwin_gui.h"

class FUZZWIN_GUI : public QMainWindow, private Ui::FUZZWIN_GUIClass
{
    Q_OBJECT

public:
    enum ButtonStatus
    {
        button_OK,
        button_NON_OK
    };

    FUZZWIN_GUI(QWidget *parent = 0);
    ~FUZZWIN_GUI();

    void initialize();  // état des boutons au démarrage
    void sendToLogWindow(const QString &msg);

private:
    QProcessEnvironment env;    // variables d'environnement du processus   

    bool isPinPresent;
    bool isZ3Present;
    bool isZ3Launched;

    
    void setButtonOk(QPushButton *b);
    void setButtonError(QPushButton *b);

    bool checkPinPath(QString &path);
    bool checkZ3Path (QString &path);
    

public slots:
    void on_GUI_selectPinButton_clicked(); // selection du répertoire de PIN
    void on_GUI_selectZ3Button_clicked(); // sélection du répertoire de Z3
    void on_GUI_selectInitialInputButton_clicked(); // sélection de l'entrée initiale
    void on_GUI_selectTargetButton_clicked();       // sélection du programme cible
    void on_GUI_selectResultsDirButton_clicked();   // sélection du répertoire de résultats
};

extern FUZZWIN_GUI *window;

#endif // FUZZWIN_GUI_H
