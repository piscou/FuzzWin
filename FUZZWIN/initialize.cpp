#include "fuzzwin.h"
#include "initialize.h"
#include "solver.h"

// PARSE COMMAND LINE : GETOPT_PP
// documentation : https://code.google.com/p/getoptpp/wiki/Documentation?tm=6
// seule modiifcation apportée au code : désactivation du warning 4290
#include "getopt_pp.h"

static std::string getExePath() // renvoie le répertoire de l'executable
{
    char buffer[MAX_PATH];
    GetModuleFileName(NULL, buffer, MAX_PATH );
    std::string::size_type pos = std::string(buffer).find_last_of("\\/");
    return (std::string(buffer).substr(0, pos + 1)); // antislash inclus
}

static inline bool testFileExists(const std::string &name)
{
    std::ifstream f(name.c_str());
    bool isExists = f.good();
    f.close();
    
    return (isExists);
}

static std::string getAbsoluteFilePath(const std::string &s)
{
    char absolutepath[MAX_PATH];
    LPSTR* a = nullptr;

    // transformation du chemin relatif en chemin absolu
    GetFullPathName((LPCSTR) s.c_str(), MAX_PATH, absolutepath, a);

    return (std::string(absolutepath));
}

static int getNativeArchitecture()
{
    BOOL isX64 = true; // par défaut on considère qu'on est en 64 bits

#if !(_WIN64)
    // en 32 bits, tester via isWow64 (source MSDN)
    typedef BOOL (WINAPI *LPFN_ISWOW64PROCESS) (HANDLE, PBOOL);
    LPFN_ISWOW64PROCESS fnIsWow64Process;

    fnIsWow64Process = (LPFN_ISWOW64PROCESS) GetProcAddress(
        GetModuleHandle(TEXT("kernel32")),"IsWow64Process");

    if (NULL != fnIsWow64Process) fnIsWow64Process(GetCurrentProcess(),&isX64);
#endif  

    return (isX64);
}

void showHelp()
{
    std::cout << "FuzzWin - Fuzzer automatique sous plateforme Windows\n";
    std::cout << " Usage : fuzzwin -t -i [-k] [-m] etc....";
}

//Effacement du contenu d'un répertoire sans l'effacer lui meme (source StackOverflow)
static int deleteDirectory(const std::string &refcstrRootDirectory, bool bDeleteSubdirectories = true)
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
                    if (SetFileAttributes(strFilePath.c_str(), FILE_ATTRIBUTE_NORMAL) == FALSE) return GetLastError();

                    // Delete file
                    if (DeleteFile(strFilePath.c_str()) == FALSE) return GetLastError();
                }
            }
        } while(FindNextFile(hFile, &FileInformation) == TRUE);

        // Close handle
        FindClose(hFile);

        DWORD dwError = GetLastError();
        if (dwError != ERROR_NO_MORE_FILES)  return dwError;
    }
    return 0;
}

std::string initialize(int argc, char** argv) 
{
    /********************************************************/
    /** récupération des arguments de la ligne de commande **/
    /********************************************************/
    GetOpt::GetOpt_pp ops(argc, argv);

    // Option -h // --help : affichage de l'aide et de l'usage, et retour immédiat
    if (ops >> GetOpt::OptionPresent('h', "help"))
    {
        showHelp();
        exit(0);
    }
    
    // afifchage du bandeau d'information
    std::cout << infoHeader << std::endl;

    /**********************************************************************/
    /** Construction des chemins d'accès aux outils externes (PIN et Z3) **/
    /**********************************************************************/
    
    std::string pin_X86, pin_X86_VmDll, pintool_X86;
    std::string pin_X64, pin_X64_VmDll, pintool_X64;
    std::string z3Path;
    
    // repertoire 'root' du launcher
    std::string exePath = getExePath(); 
    // repertoire 'root' de PIN
    std::string pinPath(getenv("PIN_ROOT"));

    // modules 32 bits 
    pin_X86       = pinPath + "ia32\\bin\\pin.exe";
    pin_X86_VmDll = pinPath + "ia32\\bin\\pinvm.dll";
    pintool_X86   = exePath + "fuzzwinX86.dll";

    pin_X64       = pinPath + "intel64\\bin\\pin.exe";
    pin_X64_VmDll = pinPath + "intel64\\bin\\pinvm.dll";
    pintool_X64   = exePath + "fuzzwinX64.dll";
    
    if (!testFileExists(pin_X86))       return "executable PIN 32bits absent";
    if (!testFileExists(pin_X86_VmDll)) return "librairie PIN_VM 32bits absente";
    if (!testFileExists(pintool_X86))   return "pintool FuzzWin 32bits absent";
    if (!testFileExists(pin_X64))       return "executable PIN 64bits absent";
    if (!testFileExists(pin_X64_VmDll)) return "librairie PIN_VM 64bits absente";
    if (!testFileExists(pintool_X64))   return "pintool FuzzWin 64bits absent";
    
    // détermination de la plateforme pour Z3
  
    int isHost64bits = getNativeArchitecture();
    
    z3Path = exePath + ((isHost64bits) ? "z3_x64.exe" : "z3_x86.exe");
    if (!testFileExists(z3Path))     return "solveur z3 absent";

    /********************************************************/
    /** exploitation des arguments de la ligne de commande **/
    /********************************************************/
    
    // option -r / --range : liste type impression des octets a tester
    // si option non présente : tous les octets du fichier seront marqués
    if (! (ops >> GetOpt::Option('r', "range", pGlobals->bytesToTaint))) 
    {
        pGlobals->bytesToTaint = "all";
    }
    
    // option -k / --keepfiles
    // conservation de tous les fichiers (entrées générées et formules issues du pintool)
    ops >> GetOpt::OptionPresent('k', "keepfiles", pGlobals->keepFiles);
    
    // option -t / --target : executable cible
    std::string targetPath;
    if (! (ops >> GetOpt::Option('t', "target", targetPath)))   return "option -t (executable cible) absente";
    if (! testFileExists(targetPath)) return "Executable cible non trouvé";

    // test du type d'exécutable. Si non supporté => quitter
    DWORD kindOfExe = 0;
    BOOL result = GetBinaryType((LPCSTR) targetPath.c_str(), &kindOfExe);
    if (!result) return ("le fichier" + targetPath + " n'est pas executable");

#if _WIN64 
    // SAGE en x64=> l'executable doit être en 64bits
    if (kindOfExe != SCS_64BIT_BINARY) return (targetPath + " n'est pas executable 64bits");
#else
    // SAGE en x86=> l'executable doit être en 32bits
   if (kindOfExe != SCS_32BIT_BINARY) return (targetPath + " n'est pas executable 32bits");
   #endif

    // option -i // --initial : premier fichier d'entrée
    std::string initialInputPath;
    if (! (ops >> GetOpt::Option('i', "initial", initialInputPath))) 
    {
        return "option -i (fichier initial) absente";
    }
    if (! testFileExists(initialInputPath))  return "Fichier initial non trouvé";

    // option -d // --destination : dossier de destination.
    // Si option non présente : choisir par défaut "results"
    std::string resultDir;
    bool isDirectoryOptionPresent = (ops >> GetOpt::Option('d', "destination", resultDir));
    if (!isDirectoryOptionPresent) resultDir = exePath + "results";

    // option -m // --maxtime : temps maximal d'execution d'une entree
    ops >> GetOpt::Option('m', "maxtime", pGlobals->maxExecutionTime);
   
    /********************************************/
    /** initialisation du dossier de resultats **/
    /********************************************/

    // création du dossier de résultats. 
    BOOL createDirResult = CreateDirectory(resultDir.c_str(), NULL);
    if (!createDirResult && (GetLastError() == ERROR_ALREADY_EXISTS))
    {
        char c;
        
        std::cout << "Le dossier de resultat existe deja\n";
        std::cout << "effacer son contenu et continuer ? (o/n)";

        do { std::cin >> c;	} while ((c != 'o') && (c != 'n'));
        if (tolower(c) == 'n')	return "";
        else if (deleteDirectory(resultDir)) return "erreur creation dossier resultats";
    }  

    // copie du fichier initial dans ce dossier (sans extension, avec le nom 'input0')
    std::string firstFileName = resultDir + "\\input0";
    CopyFile(initialInputPath.c_str(), firstFileName.c_str(), false);

    /**********************************************/
    /** création des tubes nommé avec le Pintool **/
    /**********************************************/
    pGlobals->hPintoolPipe = CreateNamedPipe("\\\\.\\pipe\\fuzzwin",	
        PIPE_ACCESS_DUPLEX,	// accès en lecture/écriture 
        PIPE_TYPE_MESSAGE | PIPE_READMODE_MESSAGE | PIPE_WAIT, // mode byte, bloquant
        1,		// une seule instance
        4096,	// buffer de sortie 
        4096,	// buffer d'entrée
        0,		// time-out du client = defaut
        NULL);	// attributs de securité par defaut

    if (pGlobals->hPintoolPipe == INVALID_HANDLE_VALUE) 
    {
        return "Erreur de creation du pipe fuzzWin\n";
    }

    /**********************************************************/
    /** création du process Z3 avec redirection stdin/stdout **/ 
    /**********************************************************/
    if (!createSolverProcess(z3Path)) 	return "erreur creation processus Z3";

    /******************************************/
    /** stockage dans les variables globales **/ 
    /******************************************/

    pGlobals->resultDir  = getAbsoluteFilePath(resultDir);
    pGlobals->targetFile = getAbsoluteFilePath(targetPath);
    pGlobals->faultFile  = pGlobals->resultDir + "\\fault.txt"; 

    // création de la ligne de commande pour le processus pin/fuzzwin
    /* $(pin_X86) 
        -p64 $(pin_X64) 
        -t64 $(pintool_X64) 
        -t $(pintool_X86) 
        -- $(targetPath) %INPUT% (ajouté a chaque fichier testé) */
    
    pGlobals->cmdLinePin = '"' + pin_X86  \
            + "\" -p64 \"" + pin_X64      \
            + "\" -t64 \"" + pintool_X64  \
            + "\" -t \""   + pintool_X86  \
            + "\" -- \"" + pGlobals->targetFile + "\" ";

    return "OK";
}
