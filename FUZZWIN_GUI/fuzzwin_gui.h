#ifndef FUZZWIN_GUI_H
#define FUZZWIN_GUI_H

#include <QtWidgets/QMainWindow>
#include "ui_fuzzwin_gui.h"

class FUZZWIN_GUI : public QMainWindow
{
    Q_OBJECT

public:
    FUZZWIN_GUI(QWidget *parent = 0);
    ~FUZZWIN_GUI();

private:
    Ui::FUZZWIN_GUIClass ui;

public slots:
    void on_Q_selectPin_clicked(); // selection du répertoire de PIN
    void on_Q_selectZ3_clicked(); // sélection du répertoire de Z3
    void on_Q_selectInitialInput_clicked(); // sélection de l'entrée initiale
    void on_Q_selectTarget_clicked();       // sélection du programme cible
    void on_Q_selectResultsDir_clicked();   // sélection du répertoire de résultats
};

#endif // FUZZWIN_GUI_H
