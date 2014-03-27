#pragma once
#include <iostream>

#include "../FUZZWIN_COMMON/fuzzwin_algo.h"

// création de la classe algorithme adapté à la ligne de commande

class FuzzwinAlgorithm_cmdLine : public FuzzwinAlgorithm
{    
private:  
    /**  implémentation des méthodes virtuelles pures **/

    void log(const std::string &msg) const;        // envoi en console
    void logVerbose(const std::string &msg) const; // idem en mode verbose
    void logVerboseEndOfLine() const;
    void logEndOfLine() const;
    void logTimeStamp() const;
    void logVerboseTimeStamp() const;

    // renvoie le répertoire ou se trouve l'executable
    std::string getExePath() const;
    // test de l'existence d'un fichier
    bool testFileExists(const std::string &filePath) const;
    // Effacement du contenu du répertoire de résultats sans l'effacer lui meme
    int deleteDirectory(const std::string &refcstrRootDirectory) const;

public:
    explicit FuzzwinAlgorithm_cmdLine(OSTYPE osType);

    // initialisation des variables de la classe
    std::string initialize(int argc, char** argv);
};
