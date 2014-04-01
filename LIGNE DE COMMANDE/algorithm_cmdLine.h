#pragma once
#include <iostream>
#include <ctime> // statistiques de temps

#include "../ALGORITHME/algorithm.h"

// création de la classe algorithme adapté à la ligne de commande

class FuzzwinAlgorithm_cmdLine : public FuzzwinAlgorithm
{    
private:  
    clock_t _timeBegin, _timeEnd;
    
    /**  implémentation des méthodes virtuelles pures de log **/
    
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

    // implémentation des méthodes virtuelles pures de contrôle de l'algorithme
    void algorithmFinished();
    void algorithmTraceOnlyFinished() {} // non implémenté pour l'instant
    void notifyAlgoIsPaused()         {} // non implémenté pour l'instant
    void faultFound()           { ++_nbFautes; }
};
