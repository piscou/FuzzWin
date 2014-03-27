// PARSE COMMAND LINE : GETOPT_PP
// documentation : https://code.google.com/p/getoptpp/wiki/Documentation?tm=6
// seule modiifcation apportée au code : désactivation du warning 4290
#include "getopt_pp.h"
#include "fuzzwin_cmdLine.h"

static const std::string helpMessage
(
"\n"
"FuzzWin - Fuzzer automatique sous plateforme Windows\n"
"\n"
"Usage:  fuzzwin.exe -t <targetExe> - i <firstInput> [options]\n"
"\n"
"Options:\n"
"--help        \t : affiche ce message\n"
"--keepfiles   \t : conserve les fichiers intermédiaires\n"
"--range       \t : intervalles d'octets à marquer (ex: 1-10;15;17-51)\n"
"--dir         \t : répertoire de sortie (défaut : './results/')\n"
"--maxconstraints : nombre maximal de contraintes à récuperer\n"
"--maxtime     \t : temps limite d'exécution de l'exécutable étudie\n"
"--score       \t : calcul du score de chaque fichier\n"
"--verbose     \t : mode verbeux\n"
"--timestamp   \t : ajout de l'heure aux lignes de log\n"
);

FuzzwinAlgorithm_cmdLine::FuzzwinAlgorithm_cmdLine(OSTYPE osType)
    : FuzzwinAlgorithm(osType) {}

// renvoie le répertoire ou se trouve l'executable
std::string FuzzwinAlgorithm_cmdLine::getExePath() const
{
    char buffer[MAX_PATH];
    GetModuleFileName(NULL, buffer, MAX_PATH);
    std::string::size_type pos = std::string(buffer).find_last_of("\\/");
    return (std::string(buffer).substr(0, pos + 1)); // antislash inclus
}

// test de l'existence d'un fichier
bool FuzzwinAlgorithm_cmdLine::testFileExists(const std::string &filePath) const
{
    std::ifstream f(filePath.c_str());
    bool isExists = f.good();
    f.close();
    
    return (isExists);
}

// Effacement du contenu d'un répertoire sans l'effacer lui meme
// source StackOverflow : http://stackoverflow.com/questions/734717/how-to-delete-a-folder-in-c
int FuzzwinAlgorithm_cmdLine::deleteDirectory(const std::string &refcstrRootDirectory) const
{
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
                    // Delete subdirectory
                    int iRC = deleteDirectory(strFilePath); 
                    if (iRC) return iRC;   
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
std::string FuzzwinAlgorithm_cmdLine::initialize(int argc, char** argv) 
{
    std::string initialInputPath;               // chemin vers l'entrée initiale
    std::string exePath = this->getExePath();   // dossier racine de l'exécutable
    
    // parsing de la ligne de commande
    GetOpt::GetOpt_pp ops(argc, argv);

    // Option -h / --help : affichage de l'usage et retour immédiat
    if (ops >> GetOpt::OptionPresent('h', "help"))
    {
        std::cout << helpMessage;
        exit(0);
    }

    // affichage du bandeau d'information
    std::cout << infoHeader << std::endl;
    
    // option --verbose : mode verbeux. Option présente = activée
    ops >> GetOpt::OptionPresent("verbose", _verbose);
    this->logVerbose("Mode verbeux ON"); 
    this->logVerboseEndOfLine();

    // argument -t / --target : exécutable cible
    if (ops >> GetOpt::Option<std::string>('t', "target", _targetPath))
    {
        _targetPath = getAbsoluteFilePath(_targetPath);

        // test du type d'exécutable (32 ou 64 bits)
        int kindOfExe = getKindOfExecutable(_targetPath);
        if (kindOfExe < 0)  return (_targetPath + " : fichier introuvable ou non exécutable");
        
        // exécutable 64bits sur OS 32bits => problème
        else if ((SCS_64BIT_BINARY == kindOfExe) && (_osType < BEGIN_HOST_64BITS))
        {
            return ("exécutable 64bits incompatible avec OS 32bits");
        }
    }
    else return ("argument -t (exécutable cible) absent");    

    // argument -i // --initial : premier fichier d'entrée
    if (ops >> GetOpt::Option<std::string>('i', "initial", initialInputPath))
    {
        if (!testFileExists(initialInputPath))  return ("fichier initial non trouvé"); 
    }
    else return ("argument -i (fichier initial) absent");

    // option --dir : dossier de destination. "results" par défaut
    if (! (ops >> GetOpt::Option<std::string>("dir", _resultsDir))) _resultsDir = exePath + "results";
    // création du dossier de résultats. 
    BOOL createDirResult = CreateDirectory(_resultsDir.c_str(), NULL);
    if (!createDirResult) // erreur de la création
    {
        if (ERROR_ALREADY_EXISTS == GetLastError())
        {
            char c;
        
            this->log ("Le dossier de résultats existe déjà");
            this->logEndOfLine();
            this->log("effacer son contenu et continuer ? (o/n)");

            do { std::cin >> c;	} while ((c != 'o') && (c != 'n'));

            if ('n' == tolower(c))	return ("");

            int eraseDir = deleteDirectory(_resultsDir);
            if (eraseDir) return ("erreur création du dossier de résultats");
            else
            {
                this->logVerbose("Création dossier resultats : OK");
                this->logVerboseEndOfLine();
            }
        }
    }
    // prise du dossier de résultats en chemin absolu
    _resultsDir = getAbsoluteFilePath(_resultsDir);
    
    // option --range : liste type impression des octets a tester (défaut = "all")
    ops >> GetOpt::Option<std::string>("range", _bytesToTaint, "all");
    this->logVerbose("Octets à suivre           : " + _bytesToTaint);
    this->logVerboseEndOfLine();
    
    // option --maxconstraints : nombre maximal de contraintes (défaut = 0)
    ops >> GetOpt::Option<UINT32>("maxconstraints", _maxConstraints, 0);   
    this->logVerbose("Contraintes max           : ");
    if (_maxConstraints) this->logVerbose(std::to_string(_maxConstraints));
    else                 this->logVerbose("N/A");
    this->logVerboseEndOfLine();
    
    // option --maxtime : temps maximal d'execution d'une entree (défaut = 0)
    ops >> GetOpt::Option<UINT32>("maxtime", _maxExecutionTime, 0);
    this->logVerbose("Temps max                 : ");
    if (_maxExecutionTime) this->logVerbose(std::to_string(_maxExecutionTime));
    else                   this->logVerbose("N/A");
    this->logVerboseEndOfLine();

    // option --keepfiles : conservation de tous les fichiers. Option présente = activée
    ops >> GetOpt::OptionPresent("keepfiles", _keepFiles);
    this->logVerbose("Option keepfiles          : ");
    if (_keepFiles) this->logVerbose("oui");
    else            this->logVerbose("non");
    this->logVerboseEndOfLine();

    // option --score : calcul du score de chaque nouveau fichier. Option présente = activée
    ops >> GetOpt::OptionPresent("score", _computeScore);
    this->logVerbose("Option score              : ");
    if (_computeScore) this->logVerbose("oui");
    else               this->logVerbose("non");
    this->logVerboseEndOfLine();
 
    // option --timestamp : ajout de l'heure aux lignes de log
    ops >> GetOpt::OptionPresent("timestamp", _timeStamp);
    this->logVerbose("Horodatage des log        : ");
    if (_timeStamp) this->logVerbose("oui");
    else            this->logVerbose("non");
    this->logVerboseEndOfLine();

    // option --hash : calcul des hash des fichiers pour éviter les doublons
    ops >> GetOpt::OptionPresent("hash", _hashFiles);
    this->logVerbose("Hash des fichiers         : ");
    if (_hashFiles) this->logVerbose("oui");
    else            this->logVerbose("non");
    this->logVerboseEndOfLine();

    // recopie de l'entrée initiale dans le dossier de résultat (sans extension, avec le nom 'input0')
    std::string firstFilePath(_resultsDir + "\\input0");
    // copie de l'entrée initiale dans le dossier de résultat
    if (!CopyFile(initialInputPath.c_str(), firstFilePath.c_str(), false))
    {
        return ("erreur de recopie du fichier initial");
    }
    // construction de l'objet représentant cette première entrée 
    _pCurrentInput = new CInput(firstFilePath, _keepFiles);
    // chemin prérempli pour le fichier de fautes (non créé pour l'instant) + conversion en chemin absolu
    _faultFile = getAbsoluteFilePath(_resultsDir + "\\fault.txt");
  
    /**********************************************************************/
    /** Construction des chemins d'accès aux outils externes (PIN et Z3) **/
    /**********************************************************************/
    
    std::string pin_X86, pin_X86_VmDll, pintool_X86;
    std::string pin_X64, pin_X64_VmDll, pintool_X64;
    
    // repertoire 'root' de PIN P1 = en variable d'environnement, P2 = répertoire de l'exécutable
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
    if (_osType >= BEGIN_HOST_64BITS) 
    {
        if (!testFileExists(pin_X64))       return "executable PIN 64bits absent";
        if (!testFileExists(pin_X64_VmDll)) return "librairie PIN_VM 64bits absente";
        if (!testFileExists(pintool_X64))   return "pintool FuzzWin 64bits absent";
    }
  
    /********************************************/
    /** création du tube nommé avec le Pintool **/
    /********************************************/
    this->logVerbose("Tube nommé avec pintool   : ");
    if (this->createNamedPipePintool())
    {
        this->logVerbose("OK");
        this->logVerboseEndOfLine();
    }
    else 
    {
        this->logVerbose("ERREUR");
        return ("");
    }

    /**********************************************************/
    /** création du process Z3 avec redirection stdin/stdout **/ 
    /**********************************************************/
    this->logVerbose("Processus du solveur  : ");
    if (this->createSolverProcess(z3Path))
    {
        this->logVerbose("OK");
        this->logVerboseEndOfLine();
    }
    else 
    {
        this->logVerbose("ERREUR");
        return ("");
    }

    /***************************************/
    /** Ligne de commande pour le pintool **/ 
    /***************************************/

    // si OS 32 bits, pas la peine de spécifier les modules 64bits
    if (_osType < BEGIN_HOST_64BITS) 
    {
        /* $(pin_X86) -t $(pintool_X86) -- $(targetFile) %INPUT% (ajouté a chaque fichier testé) */
        _cmdLinePin = '"' + pin_X86 \
             + "\" -t \"" + pintool_X86  \
             + "\" -- \"" + _targetPath + "\" ";
    }
    else
    {
        /* $(pin_X86) -p64 $(pin_X64) -t64 $(pintool_X64) -t $(pintool_X86) 
        -- $(targetFile) %INPUT% (ajouté a chaque fichier testé) */
        _cmdLinePin = '"'  + pin_X86  \
            + "\" -p64 \"" + pin_X64  \
            + "\" -t64 \"" + pintool_X64  \
            + "\" -t \""   + pintool_X86  \
            + "\" -- \""   + _targetPath + "\" ";
    }

    /*****************************************/
    /*** CREATION DU TIMER (SI NECESSAIRE) ***/
    /*****************************************/
    if (_maxExecutionTime)
    {
        _hTimer = CreateWaitableTimer(NULL /* attricuts par défaut */, TRUE /* timer manuel */, NULL /* anonyme */);
        if (NULL == _hTimer) return ("Erreur de création du timer");
    }

    this->logVerbose("!!! LANCEMENT DE L'ALGORITHME !!!");
    this->logVerboseEndOfLine();

    return ("OK");
}

/* IMPLEMENTATION DES FONCTIONS DE LOG */

// log "simple"
void FuzzwinAlgorithm_cmdLine::log(const std::string &msg) const 
{ 
    std::cout << msg; 
}

// horodatage
void FuzzwinAlgorithm_cmdLine::logTimeStamp() const 
{ 
    SYSTEMTIME st;
    char timeStamp[32];    
    
    if (!_timeStamp) return;

    GetLocalTime(&st);
    sprintf(&timeStamp[0], "[%02d:%02d:%02d:%03d] ", st.wHour, st.wMinute, st.wSecond, st.wMilliseconds);
    std::cout << &timeStamp[0];
}

// fin de ligne
void FuzzwinAlgorithm_cmdLine::logEndOfLine() const 
{ 
    std::cout << std::endl;
}

void FuzzwinAlgorithm_cmdLine::logVerbose(const std::string &msg) const 
{ 
    if (_verbose) std::cout << msg;  
}

// horodatage
void FuzzwinAlgorithm_cmdLine::logVerboseTimeStamp() const 
{
    if (_verbose) this->logTimeStamp();  
}

void FuzzwinAlgorithm_cmdLine::logVerboseEndOfLine() const 
{ 
    if (_verbose) std::cout << std::endl;  
}