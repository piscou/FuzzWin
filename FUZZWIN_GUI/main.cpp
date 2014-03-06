#include "fuzzwin_gui.h"
#include "fuzzwin.h"    // fichier commun à l'interface GUI et non-GUI
#include <QtWidgets/QApplication>

CGlobals *pGlobals;

int main(int argc, char *argv[])
{
    // initialisation des variables globales
    pGlobals = new CGlobals;
  
    if (!pGlobals) return (EXIT_FAILURE);
    
    QApplication a(argc, argv);
    FUZZWIN_GUI w;
   
    w.show();
    return a.exec();
}
