#pragma once
#pragma warning (disable:4129) // séquence d'échappement de l'expression rationnelle

#include <windows.h>
#include <process.h>

#include <iostream>	// cin et cout
#include <cstdio>   // remove (effacement fichier)
#include <cstdint>  // uint8_t etc...
#include <fstream>	// ofstream / ifstream
    
#include <string>	
#include <vector>
#include <regex>
#include <set> // table de hachage

typedef uint8_t		UINT8;
typedef uint32_t	UINT32;
typedef uint64_t	UINT64;
typedef std::set<size_t> HashTable; // stockage des hashes des fichiers déjà générés

/* solutions fournies par le solveur sont du type
   define OFF?? (_BitVec 8) 
      #x??    */ 
#define parseZ3ResultRegex "OFF(\\d+).*\r\n.*([0-9a-f]{2})"

// mode verbeux : affichage des infos sur la console
#define VERBOSE(x) { if (pGlobals->verbose) { std::cout << x; }}

// codes définissant le type d'OS pour la détermination des numéros d'appels systèmes
// Le type d'OS est déterminé par fuzzwin.exe et passé en argument au pintool
enum OSTYPE 
{
    HOST_X86_2000,
    HOST_X86_XP,
    HOST_X86_2003,

    // pour cette version, le syscall 'setinformationfile' est différent des autres SP...
    HOST_X86_VISTA_SP0, 
    HOST_X86_VISTA,
    HOST_X86_2008 = HOST_X86_VISTA,   // les index des syscalls sont les mêmes
    HOST_X86_2008_R2 = HOST_X86_2008, // les index des syscalls sont les mêmes
  
    HOST_X86_SEVEN,
    
    HOST_X86_WIN80,
    HOST_X86_2012 = HOST_X86_WIN80, 
    
    HOST_X86_WIN81,
    HOST_X86_2012_R2 = HOST_X86_WIN81, // a priori ce sont les memes
    
    BEGIN_HOST_64BITS,
    HOST_X64_BEFORE_WIN8 = BEGIN_HOST_64BITS,
    HOST_X64_WIN80,
    HOST_X64_WIN81,
    HOST_UNKNOWN
};

class CGlobals 
{
public:   
    std::string resultDir;      // dossier de résultats
    std::string faultFile;      // fichier texte retracant les fautes trouvées
    std::string targetPath;     // exécutable fuzzé
    std::string bytesToTaint;   // intervelles d'octets à surveiller
    std::string firstInputPath; // entrée initiale

    std::string cmdLinePin;	    // ligne de commande du pintool, pré-rédigée 

    OSTYPE osType;
    
    bool keepFiles;         // les fichiers sont gardés dans le dossier de resultat
    bool computeScore;      // option pour calculer le score de chaque entrée
    bool verbose;           // mode verbeux
    
    UINT32 maxExecutionTime; // temps maximal d'execution 
    UINT32 maxConstraints;   // nombre maximal de contraintes à récupérer

    HANDLE hZ3_process;	// handle du process Z3
    HANDLE hZ3_thread;	// handle du thread Z3
    HANDLE hZ3_stdout;	// handle du pipe correspondant à la sortie de Z3(= son stdout)
    HANDLE hZ3_stdin;	// handle du pipe correspondant à l'entrée de Z3 (= son stdin)
    HANDLE hReadFromZ3;	// handle pour lire les résultats de Z3
    HANDLE hWriteToZ3;	// handle pour envoyer des données vers Z3

    HANDLE hPintoolPipe; // handle du named pipe avec le pintool Fuzzwin,

    const std::regex regexModel; // pour parser les resultats du solveur

    std::hash<std::string> fileHash ; // hash d'une string : opérateur () renvoie un size_t    

    CGlobals() : 
        regexModel(parseZ3ResultRegex, std::regex::ECMAScript),
        maxExecutionTime(0), // aucun maximum de temps
        maxConstraints(0)    // pas de limite dans le nombre de contraintes
        {}

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

// détermination de l'OS dynamiquement, inspiré de l'exemple fourni sur MSDN
// le type d'OS sera passé en argument au pintool
// pour la surveillance des appels systèmes
// NB : la version 8.1 du Windows Kit a désormais des fonctions spécifiques
// mais ne sera pas utilisé ici
static inline OSTYPE getNativeArchitecture()
{
    OSTYPE osType = HOST_UNKNOWN;

    // la fonction GetNativeSystemInfo retourne une structure avec notamment
    // 'wProcessorArchitecture' qui détermine si OS 32 ou 64bits 
    SYSTEM_INFO si;
    ZeroMemory(&si, sizeof(SYSTEM_INFO));
    GetSystemInfo(&si);

    // GetVersionEx récupère la version de l'OS pour fixer le numéro des syscalls
    // la structure OSVERSIONINFOEX contient ce que l'on cherche à savoir
    OSVERSIONINFOEX osvi;
    ZeroMemory(&osvi, sizeof(osvi));
    osvi.dwOSVersionInfoSize = sizeof(OSVERSIONINFOEX);
    GetVersionEx(reinterpret_cast<OSVERSIONINFO*>(&osvi));
    // version = 10*major + minor ; permet de comparer tout de suite les nombres
    int osVersion = (10 * osvi.dwMajorVersion) + osvi.dwMinorVersion;
    
    // isWow64Process détermine si fuzzwin fonctionne en émulation 64bits.
    BOOL bIsWow64 = FALSE;
    IsWow64Process(GetCurrentProcess(), &bIsWow64);

    // Architecture de l'OS = 64 bits, ou bien émulation (Wow64)
    if ((PROCESSOR_ARCHITECTURE_AMD64 == si.wProcessorArchitecture)	|| bIsWow64)
    {
        // Avant Windows 8 (version 6.2), tous les OS 64bits
        // ont les mêmes tables pour les syscalls
        if (osVersion < 62)         osType = HOST_X64_BEFORE_WIN8;

        // Windows 8 : version 6.2
        else if (62 == osVersion)   osType = HOST_X64_WIN80;

        // pour Windows 8.1, getVersionEx est déprécié => TODO FAIRE AUTREMENT
        else if (63 == osVersion)   osType = HOST_X64_WIN81;
    }
    else if (PROCESSOR_ARCHITECTURE_INTEL == si.wProcessorArchitecture)	
    {
        switch (osVersion)	
        {
        case 50:  // Version 5.0 = Windows 2000
            osType = HOST_X86_2000;
            break;

        case 51:  // Version 5.1 = Windows XP
            osType = HOST_X86_XP;
            break;

        case 52:  // Version 5.2 = Server 2003. XP 64bits n'est pas considéré car on est en 32bits
            osType = HOST_X86_2003;
            break;

        case 60:  // Version 6.0 = Vista ou Server 2008
            if (VER_NT_WORKSTATION == osvi.wProductType) // Vista => tester le cas SP0
            {
                // le syscall 'NtSetInformationFile' diffère entre SP0 et les autres SP
                // on teste donc si un service pack est présent
                osType = (osvi.wServicePackMajor) ? HOST_X86_VISTA : HOST_X86_VISTA_SP0;
            }
            else osType = HOST_X86_2008;
            break;
       
        case 61:  // Version 6.1 = Seven ou Server 2008 R2
            osType = (VER_NT_WORKSTATION == osvi.wProductType) ? HOST_X86_SEVEN : HOST_X86_2008_R2;
            break;
     
        case 62:  // Version 6.2 = Windows 8 ou Server 2012
            osType = (VER_NT_WORKSTATION == osvi.wProductType) ? HOST_X86_WIN80 : HOST_X86_2012;
            break;

        case 63:  // Version 6.3 = Windows 8.1 ou Server 2012R2 (à voir car GetVersionEx dépréciée)
            osType = (VER_NT_WORKSTATION == osvi.wProductType) ? HOST_X86_WIN81 : HOST_X86_2012_R2;
            break;
      
        default:  // OS non reconnu donc non supporté 
            break; 
        }
    }
    return (osType);
} // getNativeArchitecture
