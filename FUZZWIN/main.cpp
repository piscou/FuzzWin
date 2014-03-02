#include "fuzzwin.h"
#include "algorithmeSearch.h"

#include <ctime>
#include <clocale>  // pour passage de la ligne de commande en francais

CGlobals *pGlobals;

int main(int argc, char *argv[]) 
{
    // passage en Francais !!!!
    std::locale locFrench("French_France.1252");
    std::locale::global(locFrench);

    // initialisation des variables globales
    pGlobals = new CGlobals;
  
    if (!pGlobals) return (EXIT_FAILURE);

    // initialisation du programme (arguments, etc...)
    // vaut "OK" si tout s'est bien passé, ou le message d'erreur sinon
    std::string initResult(initialize(argc, argv));

    if ("OK" == initResult)   
    {
        // stockage du top départ du fuzzing
        clock_t timeBegin = clock();
  
        // appel de l'algorithme "SAGE" : fonction SEARCH
        UINT32 nbFautes = algorithmeSearch();

        clock_t timeEnd = clock();

        delete (pGlobals);

        std::cout << std::endl;
        std::cout << "******************************\n";
        std::cout << "* ---> FIN DE L'ANALYSE <--- *\n";
        std::cout << "******************************\n";

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

        return (EXIT_SUCCESS);
    }
    else
    {
        std::cout << initResult << " --> ABANDON !!!" << std::endl;
        delete (pGlobals);
        return (EXIT_FAILURE);
    }
}
