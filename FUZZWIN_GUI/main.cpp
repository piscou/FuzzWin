#include "fuzzwin.h"
#include <QtWidgets/QApplication>
#include <QMessagebox>

CGlobals        *pGlobals;
FUZZWIN_GUI     *w;

int main(int argc, char *argv[])
{
    int returnValue = 0;
    QApplication a(argc, argv);

    // initialisation des variables globales
    pGlobals = new CGlobals;
    if (!pGlobals) return (EXIT_FAILURE);

    w = new FUZZWIN_GUI;
    if (!w) return (EXIT_FAILURE);

    // initialisation finale (environnement) et affichage
    w->initializeEnvironment(); 
    w->show();

    // lancement de l'application
    returnValue = a.exec();

    delete (pGlobals);
    delete (w);

    return (returnValue);
}
