#include "check.h"
#include <sstream>
#include <iomanip> // setw et setfill

HANDLE hTimoutEvent;
HANDLE hTimerThread;

static DWORD WINAPI timerThread(LPVOID lpParam)
{
    // handle du processus à monitorer, passé en argument
    HANDLE hProcess = reinterpret_cast<HANDLE>(lpParam);

    // Attente du temps imparti, ou du signal envoyé par le thread principal
    // si timeout atteint, terminer le processus de debuggage
    DWORD result = WaitForSingleObject(hTimoutEvent, (DWORD) (pGlobals->maxExecutionTime * 1000));

    if (WAIT_TIMEOUT == result) TerminateProcess(hProcess, 0);    // revoir le code de fin ???
  
    return (result);
}

// cette fonction teste si l'entrée fait planter le programme
DWORD debugTarget(CInput *pInput) 
{
    // Execution de la cible en mode debug pour récupérer la cause et l'emplacement de l'erreur
    STARTUPINFO         si; 
    PROCESS_INFORMATION pi;
    DEBUG_EVENT         e;
    
    ZeroMemory(&si, sizeof(si));
    ZeroMemory(&pi, sizeof(pi));
    ZeroMemory(&e,  sizeof(e));
    si.cb = sizeof(si);
    
    std::string cmdLineDebug(pInput->getCmdLineDebug());	
    DWORD returnCode    = 0; 
    bool  continueDebug = true;
    
    BOOL bSuccess = CreateProcess(
        nullptr,            // passage des arguments par ligne de commande
        (LPSTR) cmdLineDebug.c_str(),
        nullptr, nullptr,   // attributs de processus et de thread par défaut
        FALSE,              // pas d'héritage des handles
        DEBUG_ONLY_THIS_PROCESS | CREATE_NO_WINDOW, // mode DEBUG, pas de fenetres
        nullptr, nullptr,   // Environnement et repertoire de travail par défaut
        &si, &pi);          // Infos en entrée et en sortie
    
    if (!bSuccess)
    {
        VERBOSE("erreur createProcess Debug\n");
        return 0; // fin de la procédure prématurément
    }

    // creation d'un thread "timer" pour stopper le debuggage au bout du temps spécifié
    if (pGlobals->maxExecutionTime)
    {
        hTimerThread = CreateThread(
            nullptr, // attributs de sécurité par défaut
            0,       // taille de pile par defaut
            timerThread,    // nom de la fonction du thread
            pi.hProcess,    // argument à transmettre : le handle du processus surveillé
            0,              // attributs de creation par défaut
            nullptr);       // pas besoin du threadId de ce thread

        // création de l'évenement de fin de debuggage à cause du temps
        hTimoutEvent = CreateEvent( 
            nullptr,  // attributs de sécurité par défaut
            TRUE,     // evenement géré manuellement
            FALSE,    // état initial non signalé
            nullptr); // evenement anonyme
    }

    /**********************/
    /* DEBUT DU DEBUGGAGE */
    /**********************/
    while (continueDebug)	
    {
        // si erreur dans le debuggage : tout stopper et quitter la boucle
        if (!WaitForDebugEvent(&e, INFINITE)) 
        {
            VERBOSE("erreur WaitDebugEvent\n");
            continueDebug = false;
            break; 
        }

        // parmi les evenements, seuls les evenements "DEBUG" nous interessent
        switch (e.dwDebugEventCode) 
        { 
        // = exception (sauf cas particulier du breakpoint)
        // en particulier, le breakpoint sera déclenché à la première instruction
        case EXCEPTION_DEBUG_EVENT:
            if (e.u.Exception.ExceptionRecord.ExceptionCode != EXCEPTION_BREAKPOINT) 
            { 
                DWORD exceptionCode = e.u.Exception.ExceptionRecord.ExceptionCode;
                
                std::stringstream details;
                details << "\n\tAdresse ";
                details << std::showbase << std::hex;
                details << (void*)e.u.Exception.ExceptionRecord.ExceptionAddress;
                details << " code " << exceptionCode;

                LOG("\n\t-------------------------------------------------\n");
                LOG("\t@@@ EXCEPTION @@@ Fichier " + pInput->getFileName());
                LOG(details.str());
                LOG("\n\t-------------------------------------------------\n");
                returnCode = exceptionCode;
                continueDebug = false;
            }
            break;
        // = fin du programme. Il s'agit soit la fin normale
        // soit la fin provoqué par le thread "gardien du temps"
        case EXIT_PROCESS_DEBUG_EVENT:
            VERBOSE(" - no crash ;(\n");
            continueDebug = false;	
            // quitter la boucle 
            break;
        }
        // Acquitter dans tous les cas, (exception ou fin de programme)
        ContinueDebugEvent(e.dwProcessId, e.dwThreadId, DBG_CONTINUE);
    }

    // signaler la fin du debug. Si le timer est toujours actif, cela le libèrera
    SetEvent(hTimoutEvent);
    // fermeture des handles du programme débuggé
    CloseHandle(pi.hProcess); 
    CloseHandle(pi.hThread);
    // fermeture du handle du thread "gardien du temps"
    if (pGlobals->maxExecutionTime) CloseHandle(hTimerThread);

    // en cas d'exception levée, enregistrer l'erreur
    if (returnCode) 
    {
        // enregistrement de l'erreur dans le fichier des fautes
        // ouverture en mode "app(end)"
        std::ofstream fault(pGlobals->faultFile, std::ios::app);
        fault << pInput->getFilePath();
        fault << " Exception n° " << std::hex << returnCode << std::dec << std::endl;
        fault.close();

        // enregistrer le code d'erreur dans l'objet
        pInput->setExceptionCode(returnCode);
    }

    return (returnCode);
}
