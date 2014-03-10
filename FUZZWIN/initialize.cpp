#include "initialize.h"
#include "solver.h" 

// PARSE COMMAND LINE : GETOPT_PP
// documentation : https://code.google.com/p/getoptpp/wiki/Documentation?tm=6
// seule modiifcation apportée au code : désactivation du warning 4290
#include "getopt_pp.h"

// renvoie le répertoire ou se trouve l'executable
static std::string getExePath() 
{
    char buffer[MAX_PATH];
    GetModuleFileName(NULL, buffer, MAX_PATH);
    std::string::size_type pos = std::string(buffer).find_last_of("\\/");
    return (std::string(buffer).substr(0, pos + 1)); // antislash inclus
}

// test de l'existence d'un fichier
static inline bool testFileExists(const std::string &name)
{
    std::ifstream f(name.c_str());
    bool isExists = f.good();
    f.close();
    
    return (isExists);
}

// chemin complet d'un fichier (sans référence au dossier de travail)
static std::string getAbsoluteFilePath(const std::string &s)
{
    char absolutepath[MAX_PATH];
    LPSTR* a = nullptr;

    // transformation du chemin relatif en chemin absolu
    GetFullPathName((LPCSTR) s.c_str(), MAX_PATH, absolutepath, a);

    return (std::string(absolutepath));
}

// Usage
static void showHelp()
{
    std::cout << helpMessage;
}

//Effacement du contenu d'un répertoire sans l'effacer lui meme
// source StackOverflow : http://stackoverflow.com/questions/734717/how-to-delete-a-folder-in-c
static int deleteDirectory
    (const std::string &refcstrRootDirectory, bool bDeleteSubdirectories = true)
{
    bool            bSubdirectory = false;  // Flag, indicating whether subdirectories have been found
    HANDLE          hFile;                  // Handle to directory
    std::string     strFilePath;            // Filepath
    std::string     strPattern;             // Pattern
    WIN32_FIND_DATA FileInformation;        // File information

    strPattern = refcstrRootDirectory + "\\*.*";
    hFile = FindFirstFile(strPattern.c_str(), &FileInformation);

    if (hFile != INVALID_HANDLE_VALUE)
    {
        do
        {
            if (FileInformation.cFileName[0] != '.')
            {
                strFilePath.erase();
                strFilePath = refcstrRootDirectory + "\\" + FileInformation.cFileName;

                if (FileInformation.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
                {
                    if (bDeleteSubdirectories)
                    {
                        // Delete subdirectory
                        int iRC = deleteDirectory(strFilePath, bDeleteSubdirectories);
                        
                        if (iRC) return iRC;   
                    }
                    else bSubdirectory = true;
                }
                else
                {
                    // Set file attributes
                    if (FALSE == SetFileAttributes(strFilePath.c_str(), FILE_ATTRIBUTE_NORMAL)) 
                    {
                        return GetLastError();
                    }
                    // Delete file 
                    if (FALSE == DeleteFile(strFilePath.c_str())) return GetLastError();
                }
            }
        } while (TRUE == FindNextFile(hFile, &FileInformation));

        // Close handle
        FindClose(hFile);

        DWORD dwError = GetLastError();
        if (dwError != ERROR_NO_MORE_FILES)  return dwError;
    }
    return 0;
}

// Procédure d'initialisation de FuzzWin
// parse la ligne de commande, lance le solveur, créé le pipe, etc...
std::string initialize(int argc, char** argv) 
{
    /********************************************************/
    /** récupération des arguments de la ligne de commande **/
    /********************************************************/
    
    // repertoire du launcher
    std::string exePath = getExePath(); 
    
    GetOpt::GetOpt_pp ops(argc, argv);

    // Option -h / --help : affichage de l'usage et retour immédiat
    if (ops >> GetOpt::OptionPresent('h', "help"))
    {
        showHelp();
        exit(0);
    }

    // argument -t / --target : exécutable cible
    ops >> GetOpt::Option('t', "target", pGlobals->targetPath);  

    // argument -i // --initial : premier fichier d'entrée
    ops >> GetOpt::Option('i', "initial", pGlobals->firstInputPath);
    
    // option -r / --range : liste type impression des octets a tester
    ops >> GetOpt::Option('r', "range", pGlobals->bytesToTaint); 
        
    // option -k / --keepfiles : conservation de tous les fichiers. Option présente = activée
    ops >> GetOpt::OptionPresent('k', "keepfiles", pGlobals->keepFiles); 
   
    // option -s / --score : calcul du score de chaque nouveau fichier. Option présente = activée
    ops >> GetOpt::OptionPresent('s', "score", pGlobals->computeScore);

    // option -v / --verbose : mode verbeux. Option présente = activée
    ops >> GetOpt::OptionPresent('v', "verbose", pGlobals->verbose);

    // option -d // --destination : dossier de destination.
    ops >> GetOpt::Option('d', "dir", pGlobals->resultDir);

    // option -c // --maxconstraints : nombre maximal de contraintes
    ops >> GetOpt::Option('c', "maxconstraints", pGlobals->maxExecutionTime);
    
    // option -m // --maxtime : temps maximal d'execution d'une entree
    ops >> GetOpt::Option('m', "maxtime", pGlobals->maxExecutionTime);

    // affichage du bandeau d'information
    std::cout << infoHeader << std::endl;

    /********************************************************/
    /** exploitation des arguments de la ligne de commande **/
    /********************************************************/
    
    // test de la compatibilité de l'OS
    pGlobals->osType = getNativeArchitecture();
    if (HOST_UNKNOWN == pGlobals->osType) return ("OS non supporté");
    
    // "range" : si option non présente, tous les octets du fichier seront marqués
    if (pGlobals->bytesToTaint.empty())  pGlobals->bytesToTaint = "all";

    // "target" : exécutable cible
    pGlobals->targetPath = getAbsoluteFilePath(pGlobals->targetPath);
    if (pGlobals->targetPath.empty())  return ("argument -t (exécutable cible) absente");

    // test du type d'exécutable (32 ou 64 bits)
    int kindOfExe = getKindOfExecutable(pGlobals->targetPath);
    if (kindOfExe < 0)  return (pGlobals->targetPath + " : fichier introuvable ou non exécutable");
    // exécutable 64bits sur OS 32bits => problème
    else if ((SCS_64BIT_BINARY == kindOfExe) && (pGlobals->osType < BEGIN_HOST_64BITS))
    {
        return ("exécutable 64bits incompatible avec OS 32bits");
    }

    // "initial" : premier fichier d'entrée : test de son existence
    if (!testFileExists(pGlobals->firstInputPath))  return ("fichier initial non trouvé");

    // "destination" Si option non présente : choisir par défaut le dossier "results"
    std::string resultDir;
    ops >> GetOpt::Option('d', "dir", resultDir);
    if (pGlobals->resultDir.empty()) resultDir = exePath + "results";
    
    // création du dossier de résultats. 
    BOOL createDirResult = CreateDirectory(resultDir.c_str(), NULL);
    if (!createDirResult && (ERROR_ALREADY_EXISTS == GetLastError()))
    {
        char c;
        
        std::cout << "Le dossier de résultat existe deja\n";
        std::cout << "effacer son contenu et continuer ? (o/n)";

        do { std::cin >> c;	} while ((c != 'o') && (c != 'n'));

        if ('n' == tolower(c))	return ("");

        int eraseDir = deleteDirectory(resultDir);
        if (eraseDir) return ("erreur création du dossier de résultats");
    }  

    // copie du fichier initial dans ce dossier (sans extension, avec le nom 'input0')
    std::string firstFileName(resultDir + "\\input0");
    // récupération du chemin absolu (sans ..\..\ etc)
    firstFileName = getAbsoluteFilePath(firstFileName);
    // copie de l'entrée initiale dans le dossier de résultat
    CopyFile(pGlobals->firstInputPath.c_str(), firstFileName.c_str(), false);
    pGlobals->firstInputPath = firstFileName;

    // chemin prérempli pour le fichier de fautes (non créé pour l'instant)
    pGlobals->faultFile = pGlobals->resultDir + "\\fault.txt";
    // récupération du chemin absolu (sans ..\..\ etc)
    pGlobals->faultFile = getAbsoluteFilePath(pGlobals->faultFile);
    
    /**********************************************************************/
    /** Construction des chemins d'accès aux outils externes (PIN et Z3) **/
    /**********************************************************************/
    
    std::string pin_X86, pin_X86_VmDll, pintool_X86;
    std::string pin_X64, pin_X64_VmDll, pintool_X64;
    
    // repertoire 'root' de PIN, soit en variable d'environnement
    // sinon prendre le répertoire de fuzzwin
    std::string pinPath;
    char* pinRoot = getenv("PIN_ROOT");
    if (nullptr == pinRoot) pinPath = exePath;
    else                    
    {
        pinPath = std::string(pinRoot);
        
        // rajout du séparateur si non présent
        char lastChar = pinPath.back();
        if ((lastChar != '/') && (lastChar != '\\'))  pinPath += '\\';
    }
    // repertoire 'root' de Z3. Idem
    std::string z3Path;
    char* z3Root = getenv("Z3_ROOT");
    if (nullptr == z3Root) z3Path = exePath;
    else                   z3Path = std::string(z3Root);

    // modules 32 bits 
    pin_X86       = pinPath + "ia32\\bin\\pin.exe";
    pin_X86_VmDll = pinPath + "ia32\\bin\\pinvm.dll";
    pintool_X86   = exePath + "fuzzwinX86.dll";

    // modules 64 bits
    pin_X64       = pinPath + "intel64\\bin\\pin.exe";
    pin_X64_VmDll = pinPath + "intel64\\bin\\pinvm.dll";
    pintool_X64   = exePath + "fuzzwinX64.dll";
    
    // chemin vers Z3
    z3Path += "\\bin\\z3.exe";
    
    // test de la présence des fichiers adéquats
    if (!testFileExists(z3Path))        return "solveur z3 absent";
    
    if (!testFileExists(pin_X86))       return "executable PIN 32bits absent";
    if (!testFileExists(pin_X86_VmDll)) return "librairie PIN_VM 32bits absente";
    if (!testFileExists(pintool_X86))   return "pintool FuzzWin 32bits absent";
    // OS 32 bits : pas besoin des modules 64bits
    if (pGlobals->osType >= BEGIN_HOST_64BITS) 
    {
        if (!testFileExists(pin_X64))       return "executable PIN 64bits absent";
        if (!testFileExists(pin_X64_VmDll)) return "librairie PIN_VM 64bits absente";
        if (!testFileExists(pintool_X64))   return "pintool FuzzWin 64bits absent";
    }
  
    /**********************************************/
    /** création des tubes nommé avec le Pintool **/
    /**********************************************/
    pGlobals->hPintoolPipe = CreateNamedPipe("\\\\.\\pipe\\fuzzwin",	
        PIPE_ACCESS_DUPLEX,	// accès en lecture/écriture 
        PIPE_TYPE_MESSAGE | PIPE_READMODE_MESSAGE | PIPE_WAIT, // mode message, bloquant
        1,		// une seule instance
        4096,	// buffer de sortie 
        4096,	// buffer d'entrée
        0,		// time-out du client = defaut
        NULL);	// attributs de securité par defaut

    if (INVALID_HANDLE_VALUE == pGlobals->hPintoolPipe)
    {
        return ("Erreur de création du pipe fuzzWin\n");
    }

    /**********************************************************/
    /** création du process Z3 avec redirection stdin/stdout **/ 
    /**********************************************************/
    if (!createSolverProcess(z3Path)) 	return ("erreur création processus Z3");

    /***************************************/
    /** Ligne de commande pour le pintool **/ 
    /***************************************/

    // si OS 32 bits, pas la peine de spécifier les modules 64bits
    if (pGlobals->osType < BEGIN_HOST_64BITS) 
    {
        /* $(pin_X86) -t $(pintool_X86) -- $(targetFile) %INPUT% (ajouté a chaque fichier testé) */
        pGlobals->cmdLinePin = '"' + pin_X86 \
            + "\" -t \"" + pintool_X86       \
            + "\" -- \"" + pGlobals->targetPath + "\" ";
    }
    else
    {
        /* $(pin_X86) -p64 $(pin_X64) -t64 $(pintool_X64) -t $(pintool_X86) 
        -- $(targetFile) %INPUT% (ajouté a chaque fichier testé) */
        pGlobals->cmdLinePin = '"' + pin_X86  \
            + "\" -p64 \"" + pin_X64      \
            + "\" -t64 \"" + pintool_X64  \
            + "\" -t \""   + pintool_X86  \
            + "\" -- \""   + pGlobals->targetPath + "\" ";
    }
    
    return ("OK");
}
