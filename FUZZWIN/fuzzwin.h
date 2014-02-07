#pragma once
#pragma warning (disable:4129) // séquence d'échappement de l'expression rationnelle

#include <windows.h>
#include <process.h>

#include <iostream>	// cin et cout
#include <cstdio>   // remove (effacement fichier)
#include <cstdint>  // uint8_t etc...
#include <fstream>	// ofstream / ifstream
#include <list>		// liste de travail contenant les fichiers	
#include <string>	
#include <vector>
#include <regex>
#include <set> // table de hachage

static const std::string infoHeader(   
    "; **************************************************\n" 
    "; *  FUZZWIN : FUZZER AUTOMATIQUE SOUS WINDOWS     *\n" 
    "; *  v1.0 (c) SEBASTIEN LECOMTE 09/01/2014         *\n"
    "; *  PIN Version 2.13 kit 62732 et Z3 version 4.3  *\n"
    "; **************************************************\n" );

#if _DEBUG
#define VERBOSE(x) x
#else
#define VERBOSE(x)
#endif

class CGlobals;
class CInput;

typedef uint8_t		UINT8;
typedef uint32_t	UINT32;
typedef uint64_t	UINT64;

typedef std::list<CInput*>      ListOfInputs;
typedef std::hash<std::string>  HashValue; // hachage de chaines de caracteres : renvoie un size_t
typedef std::set<size_t>        HashTable; // stockage des hashes des fichiers déjà générés

// solutions fournies par le solveur sont du type
// define OFF?? (_BitVec 8) 
//   #x??     
#define parseZ3ResultRegex "OFF(\\d+).*\r\n.*([0-9a-f]{2})"

class CGlobals 
{
public:   
    std::string resultDir;
    std::string faultFile;
    std::string targetFile;
    std::string bytesToTaint;

    std::string cmdLinePin;	    // ligne de commande du pintool 

    bool keepFiles;          // les formules SMT2 sont enregistrées dans le dossier de resultat (option --keepfiles ou -k)
    double maxExecutionTime; // temps maximal d'execution (option --maxtime ou -m)

    HANDLE hZ3_process;	// handle du process Z3
    HANDLE hZ3_thread;	// handle du thread Z3
    HANDLE hZ3_stdout;	// handle du pipe correspondant à la sortie de Z3(= son stdout)
    HANDLE hZ3_stdin;	// handle du pipe correspondant à l'entrée de Z3 (= son stdin)
    HANDLE hReadFromZ3;	// handle pour lire les résultats de Z3
    HANDLE hWriteToZ3;	// handle pour envoyer des données vers Z3

    HANDLE hPintoolPipe; // handle du named pipe avec le pintool Fuzzwin,

    const std::regex regexModel; // expression réguliere pour parser les resultats du solveur

    std::vector<int> tokens;     // tokens utilisés dans les 2 REGEX

    CGlobals() : 
        regexModel(parseZ3ResultRegex, std::regex::ECMAScript),
        
        hZ3_process(nullptr), hZ3_thread(nullptr), hZ3_stdout(nullptr),	hZ3_stdin(nullptr),
        hReadFromZ3(nullptr), hWriteToZ3(nullptr), hPintoolPipe(nullptr),
        maxExecutionTime(0)   // aucun maximum de temps
        {
            // tokens des sous-chaines à chercher pour les regexs
            this->tokens.push_back(1); 	this->tokens.push_back(2);
        }

    ~CGlobals() 
    {
        // fermeture du processus Z3
        CloseHandle(this->hZ3_process); CloseHandle(this->hZ3_thread);
        // fermeture des différents tubes de communication avec Z3
        CloseHandle(this->hZ3_stdout); 	CloseHandle(this->hZ3_stdin);
        CloseHandle(this->hReadFromZ3);	CloseHandle(this->hWriteToZ3);
        // fermeture des tubes nommés avec le pintool Fuzzwin
        CloseHandle(this->hPintoolPipe);
    }
};

extern CGlobals *pGlobals;

#include "CInput.h"