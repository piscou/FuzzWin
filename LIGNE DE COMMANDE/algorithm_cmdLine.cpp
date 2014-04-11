// PARSE COMMAND LINE : GETOPT_PP
// documentation : https://code.google.com/p/getoptpp/wiki/Documentation?tm=6
// seule modiifcation apportée au code : désactivation du warning 4290
#include "getopt_pp.h"
#include "algorithm_cmdLine.h"

#include <chrono>

static const std::string helpMessage
(
"\n"
"FuzzWin - Fuzzer automatique sous plateforme Windows\n"
"\n"
"Usage:  fuzzwin.exe -t <targetExe> - i <firstInput> [options]\n"
"\n"
"Options pour l'algorithme:\n"
" --verbose / -v\t : mode verbeux\n"
" --help        \t : affiche ce message\n"
" --traceonly   \t : génération d'une seule trace avec le fichier d'entrée\n"
" --keepfiles   \t : conserve les fichiers intermédiaires\n"
" --dir         \t : répertoire de sortie spécifique (défaut : './results/')\n"
" --score       \t : calcul du score de chaque fichier\n"
" --timestamp   \t : ajout de l'heure aux lignes de log\n"
"Options pour le pintool:\n"
" --maxconstraints : nombre maximal de contraintes à récupérer\n"
" --maxtime     \t : temps limite d'exécution de l'exécutable étudie\n"
" --range       \t : intervalles d'octets à marquer (ex: 1-10;15;17-51)\n"
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
    /** OPTIONS DU PINTOOL ***/
    UINT32 maxConstraints;    // nombre maximal de contraintes à récupérer
    bool   logTaint;          // log du marquage de données
    bool   logAsm;            // log de dessasemblage du programme
    std::string  bytesToTaint;   // intervalles d'octets à surveiller

    std::string exePath = this->getExePath();   // dossier racine de l'exécutable
    
    // options de ligne de commande pour le pintool en mode "marquage"
    std::string cmdLineOptions("-option taint"); 
    cmdLineOptions += " -os " + std::to_string(_osType);

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
    ops >> GetOpt::OptionPresent('v', "verbose", _verbose);
    this->logVerbose("Mode verbeux ON"); 
    this->logVerboseEndOfLine();

    // argument -t / --target : exécutable cible
    if (ops >> GetOpt::Option<std::string>('t', "target", _targetPath))
    {
        _targetPath = getAbsoluteFilePath(_targetPath);

        // test du type d'exécutable (32 ou 64 bits)
        int kindOfExe = getKindOfExecutable(_targetPath);
        if (kindOfExe < 0) 
        {
            this->log(_targetPath + " : fichier introuvable ou non exécutable");
            return ("");
        }
        // exécutable 64bits sur OS 32bits => problème
        else if ((SCS_64BIT_BINARY == kindOfExe) && (_osType < BEGIN_HOST_64BITS))
        {
            return ("exécutable 64bits incompatible avec OS 32bits");
        }
    }
    else return ("argument -t (exécutable cible) absent");    

    // argument -i // --initial : premier fichier d'entrée
    if (ops >> GetOpt::Option<std::string>('i', "initial", _firstInputPath))
    {
        if (!testFileExists(_firstInputPath))  return ("fichier initial non trouvé"); 
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
    
    // option --keepfiles : conservation de tous les fichiers. Option présente = activée
    ops >> GetOpt::OptionPresent("keepfiles", _keepFiles);
    this->logVerbose("Option keepfiles           : ");
    if (_keepFiles) this->logVerbose("oui");
    else            this->logVerbose("non");
    this->logVerboseEndOfLine();

    // option --score : calcul du score de chaque nouveau fichier. Option présente = activée
    ops >> GetOpt::OptionPresent("score", _computeScore);
    this->logVerbose("Option score               : ");
    if (_computeScore) this->logVerbose("oui");
    else               this->logVerbose("non");
    this->logVerboseEndOfLine();
 
    // option --timestamp : ajout de l'heure aux lignes de log
    ops >> GetOpt::OptionPresent("timestamp", _timeStamp);
    this->logVerbose("Horodatage des log         : ");
    if (_timeStamp) this->logVerbose("oui");
    else            this->logVerbose("non");
    this->logVerboseEndOfLine();

    // option --hash : calcul des hash des fichiers pour éviter les doublons
    ops >> GetOpt::OptionPresent("hash", _hashFiles);
    this->logVerbose("Hash des fichiers          : ");
    if (_hashFiles) this->logVerbose("oui");
    else            this->logVerbose("non");
    this->logVerboseEndOfLine();

    // option --traceonly : une seule exécution avec l'entrée sélectionnée
    ops >> GetOpt::OptionPresent("traceonly", _traceOnly);
    this->logVerbose("Mode sélectionné          : ");
    if (_traceOnly) this->logVerbose(" traceonly");
    else            this->logVerbose(" normal");
    this->logVerboseEndOfLine();

    /*** OPTIONS POUR LE PINTOOL ***/

    // option --range : liste type impression des octets a tester
    // si option non présente : tout marquer
    ops >> GetOpt::Option<std::string>("range", bytesToTaint, "");
    this->logVerbose("Octets à suivre            : ");
    if (bytesToTaint.empty())
    {
        this->logVerbose("N/A");
    }
    else
    {
        this->logVerbose(bytesToTaint);
        cmdLineOptions += " -range " + bytesToTaint;
    }
    this->logVerboseEndOfLine();
    
    // option --maxconstraints : nombre maximal de contraintes (défaut = 0)
    ops >> GetOpt::Option<UINT32>("maxconstraints", maxConstraints, 0);   
    this->logVerbose("Contraintes max            : ");
    if (maxConstraints)
    {
        this->logVerbose(std::to_string(maxConstraints));
        cmdLineOptions += " -maxconstraints " + std::to_string(maxConstraints);
    }
    else this->logVerbose("N/A");
    this->logVerboseEndOfLine();
    
    // option --maxtime : temps maximal d'execution d'une entree (défaut = 0)
    // ATTENTION : variable memebre de l'algorithme
    ops >> GetOpt::Option<UINT32>("maxtime", _maxExecutionTime, 0);
    this->logVerbose("Temps max                  : ");
    if (_maxExecutionTime)
    {
        this->logVerbose(std::to_string(_maxExecutionTime));
        cmdLineOptions += " -maxtime " + std::to_string(_maxExecutionTime);
        
    }
    else this->logVerbose("N/A");
    this->logVerboseEndOfLine();

    // option --logasm : log de dessasemblage des instructions exécutées
    ops >> GetOpt::OptionPresent("logasm", logAsm);
    this->logVerbose("Log de dessasemblage       : ");
    if (logAsm)
    {
        this->logVerbose("oui");
        cmdLineOptions += " -logasm ";
    }
    else this->logVerbose("non");
    this->logVerboseEndOfLine();
   
    // option --logtaint : log de marquage des instructions exécutées
    ops >> GetOpt::OptionPresent("logtaint", logTaint);
    this->logVerbose("Log de marquage           : ");
    if (logTaint)
    {
        this->logVerbose("oui");
        cmdLineOptions += " -logtaint ";
    }
    else this->logVerbose("non");
    this->logVerboseEndOfLine();

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
    pintool_X86   = exePath + "..\\pintool\\fuzzwinX86.dll";

    // modules 64 bits
    pin_X64       = pinPath + "intel64\\bin\\pin.exe";
    pin_X64_VmDll = pinPath + "intel64\\bin\\pinvm.dll";
    pintool_X64   = exePath + "..\\pintool\\fuzzwinX64.dll";
    
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

    // chemin vers Z3 et test de son existence
    z3Path += "\\bin\\z3.exe";
    if (!testFileExists(z3Path))        return "solveur z3 absent";
    _z3Path = z3Path;
   
    // création des outils internes et externes
    int result = this->finalizeInitialization(
        pin_X86, pin_X64, pintool_X86, pintool_X64, cmdLineOptions);

    if (EXIT_FAILURE == result) return ("");

    // top départ chrono
    _timeBegin = std::chrono::system_clock::now();

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

// horodatage. TODO : rendre la fonction portable (pas d'appel à l'API Windows...)
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

// fin de l'algorithme : affichage des résultats à l'écran
void FuzzwinAlgorithm_cmdLine::algorithmFinished()
{
    // fin du chrono, et affichage du temps écoulé
    _timeEnd = std::chrono::system_clock::now();

    std::string timeElapsed;
    auto timeElapsedInMilis = std::chrono::duration_cast<std::chrono::milliseconds>(_timeEnd - _timeBegin);

    auto hoursElapsed  = std::chrono::duration_cast<std::chrono::hours>  (timeElapsedInMilis);  
    if (hoursElapsed.count())
    {
        timeElapsed = std::to_string(hoursElapsed.count()) + "h ";
        timeElapsedInMilis -= std::chrono::duration_cast<std::chrono::milliseconds>(hoursElapsed);
    }

    auto minutesElapsed = std::chrono::duration_cast<std::chrono::minutes>(timeElapsedInMilis);
    if (minutesElapsed.count())
    {
        timeElapsed += std::to_string(minutesElapsed.count()) + "m ";
        timeElapsedInMilis -= std::chrono::duration_cast<std::chrono::milliseconds>(minutesElapsed);
    }

    auto secondsElapsed = std::chrono::duration_cast<std::chrono::seconds>(timeElapsedInMilis);
    if (secondsElapsed.count())
    {
        timeElapsed += std::to_string(secondsElapsed.count()) + "s ";
        timeElapsedInMilis -= std::chrono::duration_cast<std::chrono::milliseconds>(secondsElapsed);
    }
    
    timeElapsed += std::to_string(timeElapsedInMilis.count()) + "ms";


    this->log("statistiques de temps : ");
    this->log(timeElapsed);
    this->logEndOfLine();
}
