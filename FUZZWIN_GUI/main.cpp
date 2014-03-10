#include "fuzzwin.h"
#include <QtWidgets/QApplication>
#include <QMessagebox>
//#include <qtextcodec.h>

CGlobals *pGlobals;
FUZZWIN_GUI *window;

int main(int argc, char *argv[])
{
    int returnValue = 0;

    // initialisation des variables globales
    pGlobals = new CGlobals;
    if (!pGlobals) return (EXIT_FAILURE);

    // test de la compatibilité de l'OS
    pGlobals->osType = getNativeArchitecture();
    if (HOST_UNKNOWN == pGlobals->osType)
    {
        QMessageBox::critical(nullptr, "Erreur", "L'OS hôte n'est pas supporté : abandon");
        delete (pGlobals);
        return (EXIT_FAILURE);
    }
    //QLocale loc(QLocale::French, QLocale::France);
    //QLocale::setDefault(loc);

    QApplication a(argc, argv);
    window = new FUZZWIN_GUI;
   
    window->initialize();
    window->show();
    returnValue = a.exec();

    delete (pGlobals);

    return (returnValue);
}
