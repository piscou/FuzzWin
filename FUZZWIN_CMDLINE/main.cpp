#include "fuzzwin_cmdLine.h"

#include <ctime>
#include <clocale>  // pour passage de la ligne de commande en francais

int main(int argc, char *argv[]) 
{
    int returnCode = EXIT_FAILURE;  // pessimisme

    // passage en Francais !!!!
    std::locale locFrench("French_France.1252");
    std::locale::global(locFrench);

    // test de la compatibilité de l'OS
    OSTYPE osType = getNativeArchitecture();
    if (HOST_UNKNOWN == osType)
    {
        std::cout << "OS non supporté : abandon\n";
        exit(EXIT_FAILURE);
    }
    
    FuzzwinAlgorithm_cmdLine *algo = new FuzzwinAlgorithm_cmdLine(osType);
    if (!algo) return (EXIT_FAILURE);

    // initialisation des variables à partir de la ligne de commande
    // vaut "OK" si tout s'est bien passé, ou le message d'erreur sinon
    std::string initResult = algo->initialize(argc, argv);

    if ("OK" == initResult)   
    {
        // appel de l'algorithme "SAGE" : fonction SEARCH
        clock_t timeBegin = clock();
        algo->start();
        // récupération du nombre de fautes trouvées
        clock_t timeEnd = clock();
        UINT32 nbFautes = algo->getNumberOfFaults();
        
        // permet de lancer une autre ligne de commande de suite (fermeture des handles)
       // delete (algo); 

        std::cout << std::endl;
        std::cout << "******************************\n";
        std::cout << "* ---> FIN DE L'ANALYSE <--- *\n";
        std::cout << "******************************\n";

        if (nbFautes) // si une faute a été trouvée
        { 
            std::cout << "---> " << nbFautes << " faute";
            if (nbFautes > 1) std::cout << 's';
            std::cout << " !! consultez le fichier fault.txt <---\n";
        }
        else std::cout << "* aucune faute... *\n";
        
        std::cout << "statistiques de temps : ";
        std::cout << ((float) (timeEnd - timeBegin)/CLOCKS_PER_SEC ) << " secondes\n";
        
        std::cout << "\nAppuyer sur une touche pour quitter";
        fflush(stdin);
        getchar();

        returnCode = EXIT_SUCCESS;
    }
    else
    {
        std::cout << initResult << " --> ABANDON !!!" << std::endl;
        delete (algo);
        returnCode = EXIT_FAILURE;
    }

    return (returnCode);
}
