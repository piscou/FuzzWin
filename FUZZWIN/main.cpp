#include "fuzzwin.h"
#include "initialize.h"
#include "algorithmeSearch.h"

#include <ctime>

CGlobals *pGlobals;

int main(int argc, char *argv[]) 
{
    // initialisation des variables globales
    pGlobals = new CGlobals;
  
    if (!pGlobals) return EXIT_FAILURE;

    // initialisation du programme (arguments, etc...)
    // vaut "OK" si tout s'est bien passé, ou le message d'erreur sinon
    std::string initResult(initialize(argc, argv));

    if (initResult == "OK")   
    {
        // stockage du top départ du fuzzing
        clock_t timeBegin = clock();
  
        // appel de l'algorithme "SAGE" : fonction SEARCH
        UINT32 nbFautes = algorithmeSearch();

        clock_t timeEnd = clock();

        std::cout << std::endl;
        std::cout << "; ****************************\n";
        std::cout << "; ---> FIN DE L'ANALYSE <-----\n";
        std::cout << "; ****************************\n";

        if (nbFautes) // si une faute a été trouvée
        { 
            std::cout << "---> " << nbFautes << " faute";
            if (nbFautes > 1) std::cout << "s";
            std::cout << " !! consultez le fichier fault.txt <---\n";
        }
        else std::cout << "* aucune faute... *\n";
        
        std::cout << "statistiques de temps : ";
        std::cout << ((float) (timeEnd - timeBegin)/CLOCKS_PER_SEC ) << " secondes\n";
        
        std::cout << "\n\tAppuyer sur une touche pour quitter";
        fflush(stdin);
        getchar();

        return EXIT_SUCCESS;
    }
    else
    {
        std::cout << initResult << " --> ABANDON !!!" << std::endl;
        return EXIT_FAILURE;
    }
}
