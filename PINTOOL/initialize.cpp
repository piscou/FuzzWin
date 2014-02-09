#include "pintool.h"
#include "syscalls.h"
#include "TaintManager.h"
#include "buildFormula.h"
#include "instrumentation.h"

/* ===================================================================== */
// Procedures d'initialisation
/* ===================================================================== */

// thread interne au pintool pour gerer la durée de l'instrumentation
static void maxTimeThread(void *nothing)
{
    // attente du temps spécifié
    PIN_Sleep(static_cast<UINT32>(1000 * g_maxTime));

    // Si le pintool n'a pas déjà terminé, le faire (code 2 = TIMEOUT)
    PIN_ExitApplication(2); 
} // controlThread

// ouverture du pipe de communication avec le programme FuzzWin 
static int openPipe()
{
    g_hPipe = WINDOWS::CreateFile(
            "\\\\.\\pipe\\fuzzwin", // pipe name 
            GENERIC_WRITE | GENERIC_READ, // acces en lecture/ecriture
            0,             // pas de partage 
            nullptr,       // attributs de sécurité par défaut
            OPEN_EXISTING, // pipe existant
            0,             // attributs par défaut
            nullptr);	   // pas de modèle

    if ((HANDLE)(WINDOWS::LONG_PTR) (-1) == g_hPipe)  return (EXIT_FAILURE);
    
    // Changement du mode en message
    DWORD dwMode = PIPE_READMODE_MESSAGE; 
    WINDOWS::BOOL fSuccess = WINDOWS::SetNamedPipeHandleState( 
        g_hPipe,  // handle à modifier 
        &dwMode,  // nouveau mode 
        nullptr, nullptr); // pas de maximum de longueur ni de temps 
    
    if (fSuccess)  return (EXIT_SUCCESS);
    else return (EXIT_FAILURE);
} // openPipe

static std::string readFromPipe()
{   
    // pointeur vers buffer de récupération des données
    // 1024 octets sont LARGEMENT suffisants pour chaque commande recue
    // A modifier au cas ou on aurait besoin de plus.... mais improbable   
    char buffer[1024] = {0}; 
    DWORD nbRead = 0; 
    
    // lecture de maxi 1024 octets. Le cas ERROR_MORE_DATA n'est pas testé
    // car il supposerait un message > 1024 octets
    WINDOWS::BOOL fSuccess = WINDOWS::ReadFile( 
        g_hPipe,    // handle du pipe
        &buffer[0], // adresse du buffer
        1024,       // taille à lire 
        &nbRead,    // nombre d'octets lus 
        nullptr);   // pas d'overlap
 
    // retour du message lu uniquement en cas de réussite de ReadFile
    if (fSuccess) return (std::string(&buffer[0], nbRead));    
    else return ("");
} // readFromPipe

static int initOptionTaint()
{
    // chaine de caractères définissant les intervalles d'octets à marquer
    // ils sont fournis grace à un argument (knob ou pipe)
    std::string bytesToTaint;

    /*** RECUPERATION DES ARGUMENTS ***/
#if DEBUG
    // l'écriture des resultats (formule SMT2) se fera à l'écran
    g_hPipe = WINDOWS::GetStdHandle(STD_OUTPUT_HANDLE);

    if ((HANDLE)(WINDOWS::LONG_PTR) (-1) == g_hPipe)  return (EXIT_FAILURE);

    // 1) récupération des options via la ligne de commande (KNOB)
    g_inputFile      = KnobInputFile.Value();
    g_maxTime        = KnobMaxExecutionTime.Value();
    g_maxConstraints = KnobMaxConstraints.Value();
    bytesToTaint     = KnobBytesToTaint.Value(); 

    // 2) création des fichiers de déssasemblage et de suivi du marquage
    std::string logfile  (g_inputFile + "_dis.txt");
    std::string taintfile(g_inputFile + "_taint.txt");
 
    g_debug.open(logfile);
    g_taint.open(taintfile);
    if (!g_debug.good() || !g_taint.good()) return (EXIT_FAILURE);

    // 3) stockage de l'heure du top départ pour statistiques
    g_timeBegin = clock();
#else
    // récupération des arguments envoyés dans le pipe
    // 1) chemin vers l'entrée étudiée
    g_inputFile = readFromPipe();
    // 2) nombre maximal de contraintes
    g_maxConstraints = LEVEL_BASE::Uint32FromString(readFromPipe());   
    // 3) temps limite d'execution en secondes
    g_maxTime = LEVEL_BASE::Uint32FromString(readFromPipe());
    // 4) offset des entrees a etudier
    bytesToTaint = readFromPipe();
#endif

    /*** INITIALISATION VARIABLES GLOBALES ET INSTANCIATIONS ***/
        
    // instanciation des classes globales (marquage mémoire et formule SMT2)
    pTmgrGlobal   = new TaintManager_Global;
    g_pFormula    = new SolverFormula;
    if (!pTmgrGlobal || !g_pFormula)  return (EXIT_FAILURE);
    
    // stockage des intervalles d'octets source à marquer
    // si la chaine de caractères vaut "all" tout sera marqué
    pTmgrGlobal->setBytesToTaint(bytesToTaint);

    // initialisation de variable globale indiquant le départ de l'instrumentation
    // est mise à vrai par la partie syscalls lorsque les premières données
    // marquées sont créées (= lecture dans l'entrée)
    g_beginInstrumentationOfInstructions = false;

    // création des clefs pour les TLS, pas de fonction de destruction
    g_tlsKeyTaint       = PIN_CreateThreadDataKey(nullptr);
    g_tlsKeySyscallData = PIN_CreateThreadDataKey(nullptr);

    // détermination des numéros de syscalls à monitorer (dépend de l'OS)
    SYSCALLS::defineSyscallsNumbers();

    // initialisation réussie
    return (EXIT_SUCCESS);
} // initOptionTaint

int pintoolInit()
{ 
    // Initialisation des verrous pour le multithreading
    PIN_InitLock(&g_lock);
    
    // valeur de retour (par défaut fixé à erreur d'initialisation)
    int returnValue = EXIT_FAILURE;
    
    // récupération du handle de communication
    // DEBUG   : lecture via ligne de commande, sortie en STDOUT
    // RELEASE : lecture et écriture dans pipe "fuzzwin"
    // puis récupération de l'option du pintool('taint' ou 'checkscore')
    
    #if DEBUG
    // l'écriture des resultats (formule SMT2) se fera à l'écran
    g_hPipe = WINDOWS::GetStdHandle(STD_OUTPUT_HANDLE);
    if ((HANDLE)(WINDOWS::LONG_PTR) (-1) == g_hPipe)  return (EXIT_FAILURE);
    
    std::string pintoolOption(KnobOption.Value());
    #else
    // ouverture du pipe de communication avec FuzzWin
    if (EXIT_FAILURE == openPipe()) return (EXIT_FAILURE);

    std::string pintoolOption(readFromPipe());
    #endif

    /*** OPTION TAINT ***/
    if (pintoolOption == "taint")
    {
        if (EXIT_FAILURE == initOptionTaint()) return (EXIT_FAILURE);
        returnValue = OPTION_TAINT;
    }
    /*** OPTION CHECKSCORE ***/
    else if (pintoolOption == "checkscore")
    {
        #if DEBUG
        g_maxTime = KnobMaxExecutionTime.Value();
        #else
        g_maxTime = LEVEL_BASE::Uint32FromString(readFromPipe());
        #endif

        // INITIALISATION VARIABLES GLOBALES
        g_nbIns          = 0;
        g_foundException = false;

        returnValue = OPTION_CHECKSCORE;  
    }
    // Option inconnue
    else return (EXIT_FAILURE);

    // création d'un thread interne au pintool : 
    // sert à la surveillance du temps maximal d'execution (si différent de 0)
    if (g_maxTime)
    {
        THREADID tid = PIN_SpawnInternalThread(maxTimeThread, nullptr, 0, nullptr);
        if (INVALID_THREADID == tid)   return (EXIT_FAILURE);  
    }

    return (returnValue); // option choisie (taint ou checkScore)
} // pintoolInit()