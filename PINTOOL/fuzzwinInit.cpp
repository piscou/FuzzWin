#include "pintool.h"
#include "syscalls.h"
#include "TaintManager.h"
#include "buildFormula.h"
#include "instrumentation.h"

/* ===================================================================== */
// Procedures d'initialisation
/* ===================================================================== */

// thread interne au pintool pour gerer la durée de l'instrumentation
static void controlThread(void *nothing)
{
    // attente du temps spécifié
    PIN_Sleep(static_cast<UINT32>(1000 * maxTime));
    // Si le pintool n'a pas déjà terminé, le faire (code 2 = TIMEOUT)
    PIN_ExitApplication(2); 
}

std::string readFromPipe()
{   
    // pointeur vers buffer de récupération des données
    // 1024 octets sont LARGEMENT suffisants pour chaque commande recue
    // A modifier au cas ou on aurait besoin de plus.... mais improbable   
    char buffer[1024] = {0}; 
    DWORD nbRead = 0; 
    
    // lecture de maxi 1024 octets. Le cas ERROR_MORE_DATA n'est pas testé
    // car il supposerait un message > 1024 octets
    WINDOWS::BOOL fSuccess = WINDOWS::ReadFile( 
        hPipe,      // handle du pipe
        &buffer[0], // adresse du buffer
        1024,        // taille à lire 
        &nbRead,    // nombre d'octets lus 
        nullptr);   // pas d'overlap
 
    // retour du message lu uniquement en cas de réussite de ReadFile
    if (fSuccess) return (std::string(&buffer[0], nbRead));    
    else return ("");
}

int fuzzwinInit()
{ 
    // variable globale indiquant le départ de l'instrumentation
    // est mise à vrai par la partie syscalls lorsque les premières données
    // marquées sont créées (= lecture dans l'entrée)
    beginInstrumentation = false;

    // Initialisation des verrous pour le multithreading
    PIN_InitLock(&lock);

    // création des clefs pour les TLS, pas de fonction de destruction
    tlsKeyTaint       = PIN_CreateThreadDataKey(nullptr);
    tlsKeySyscallData = PIN_CreateThreadDataKey(nullptr);

    // détermination des numéros de syscalls à monitorer (dépend de l'OS)
    SYSCALLS::defineSyscallsNumbers();

    // allocation des classes globales (marquage mémoire et formule SMT2)
    pTmgrGlobal = new TaintManager_Global;
    pFormula    = new SolverFormula;
    if (!pTmgrGlobal || !pFormula)  return 0;

#if DEBUG
    // MODE DEBUG : 
    // l'écriture des resultats (formule SMT2) se fera à l'écran
    hPipe = WINDOWS::GetStdHandle(STD_OUTPUT_HANDLE);

    // 1) récupération des options via la ligne de commande (KNOB)
    // 2) création des fichiers de déssasemblage et de suivi du marquage 

    // 3) la formule SMT2 sera envoyée à l'écran (pas de pipe)
    
    inputFile       = KnobInputFile.Value();
    maxTime         = KnobMaxExecutionTime.Value();
    maxConstraints  = KnobMaxConstraints.Value();
    std::string bytesToTaint = KnobBytesToTaint.Value();
    
    std::string logfile  (inputFile + "_dis.txt");
    std::string taintfile(inputFile + "_taint.txt");
 
    debug.open(logfile);
    if (!debug.good()) 
    {
        std::cout << "erreur creation fichier debug";
        return 0;
    }

    taint.open(taintfile);
    if (!taint.good()) 
    {
        std::cout << "erreur creation fichier taint";
        return 0;
    }
    
    // stockage de l'heure du top départ pour statistiques
    timeBegin = clock();

#else
    // ouverture du pipe de communication avec le programme d'ordonnancement des entrées
    // sert uniquement en mode RELEASE : en DEBUG la formule est imprimée sur l'écran
    // et les arguments d'entrée sont passés par ligne de commande    
    hPipe = WINDOWS::CreateFile(
         "\\\\.\\pipe\\fuzzwin", // pipe name 
         GENERIC_WRITE | GENERIC_READ, // acces en lecture/ecriture
         0,             // no sharing 
         nullptr,       // default security attributes
         OPEN_EXISTING, // opens existing pipe 
         0,             // default attributes 
         nullptr);		// no template file

    // Erreur si INVALID_HANDLE_VALUE
    if ( (HANDLE)(WINDOWS::LONG_PTR) (-1) == hPipe)  return 0;
    
    // CHANGEMENT DU MODE EN TYPE_MESSAGE
    DWORD dwMode = PIPE_READMODE_MESSAGE; 
    WINDOWS::BOOL fSuccess = WINDOWS::SetNamedPipeHandleState( 
        hPipe,    // handle à modifier 
        &dwMode,  // nouveau mode 
        nullptr, nullptr); // pas de maximum de longueur ni de temps 
    
    if ( !fSuccess)  return 0;

    // récupération des arguments depuis le programme d'ordonnancement
    // 1) chemin vers l'entrée étudiée
    inputFile = readFromPipe();

    // 2) nombre maximal de contraintes
    maxConstraints = LEVEL_BASE::Uint32FromString(readFromPipe());
    
    // 3) temps limite d'execution en secondes
    maxTime = LEVEL_BASE::Uint32FromString(readFromPipe());

    // 4) offset des entrees a etudier
    std::string bytesToTaint = readFromPipe();   
#endif

    // stockage des intervalles d'octetts source à marquer
    // si la chaine de caractères vaut "all" tout sera marqué
    pTmgrGlobal->setBytesToTaint(bytesToTaint);

    // création d'un thread interne au pintool : 
    // sert à la surveillance du temps maximal d'execution (si différent de 0)
    if (maxTime)
    {
        if (INVALID_THREADID == PIN_SpawnInternalThread(controlThread, nullptr, 0, nullptr)) 
        { 
            return 0;   // = erreur d'init
        }
    }
    return 1; // Tout est OK
}