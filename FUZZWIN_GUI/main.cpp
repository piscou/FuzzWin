#include "fuzzwin_gui.h"
#include <QtWidgets/QApplication>
#include <QMessagebox>

int main(int argc, char *argv[])
{
    QApplication a(argc, argv);
    FUZZWIN_GUI w;

    // initialisation finale (environnement) et affichage
    w.initializeEnvironment(); 
    w.show();

    // lancement de l'application
    return (a.exec());
}
