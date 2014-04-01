#include "algorithm.h"

// cette fonction teste si l'entrée fait planter le programme
DWORD FuzzwinAlgorithm::debugTarget(CInput *pNewInput) 
{
    // Execution de la cible en mode debug pour récupérer la cause et l'emplacement de l'erreur
    STARTUPINFO         si; 
    PROCESS_INFORMATION pi;
    DEBUG_EVENT         e;
    
    ZeroMemory(&si, sizeof(si));
    ZeroMemory(&pi, sizeof(pi));
    ZeroMemory(&e,  sizeof(e));
    si.cb = sizeof(si);
    
    std::string cmdLineDebug(this->getCmdLineDebug(pNewInput));	
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
        this->logTimeStamp();
        this->log("    Erreur createProcess Debug");
        this->logEndOfLine();
        return 0; // fin de la procédure prématurément
    }

    // activation du "timer" pour stopper le debuggage au bout du temps spécifié
    if (_hTimer)
    {
        // transformation secondes => intervalles de 100 nanosecondes ( x (-10 000 000))
        LARGE_INTEGER liDueTime;
        liDueTime.QuadPart = _maxExecutionTime * (-10000000LL);

        if (!SetWaitableTimer(_hTimer,
            &liDueTime, // temps d'attente
            0,          // pas de périodicité
            &FuzzwinAlgorithm::timerExpired,    // fonction appelée lors de l'expiration
            &pi.hProcess, // argument passé : handle du processus en cours de debuggage
            0)) // peu importe le 'resume'
        {
            this->logTimeStamp();
            this->log("    Erreur Lancement du timer !!");
            this->logEndOfLine();
            return 0;
        }
    }

    /**********************/
    /* DEBUT DU DEBUGGAGE */
    /**********************/
    while (continueDebug)	
    {
        // si erreur dans le debuggage : tout stopper et quitter la boucle
        if (!WaitForDebugEvent(&e, INFINITE)) 
        {
            this->logVerboseTimeStamp();
            this->logVerbose("    Erreur WaitDebugEvent");
            this->logVerboseEndOfLine();
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
                PVOID exceptionAddr = e.u.Exception.ExceptionRecord.ExceptionAddress;
                char details[64];

                sprintf(&details[0], " Adresse 0x%p - Code %08X", exceptionAddr, exceptionCode);
                
                this->logEndOfLine();
                this->log(std::string(60, '*'));
                this->logEndOfLine();

                this->logTimeStamp();
                this->log(" @@@ ERREUR @@@ Fichier " + pNewInput->getFileName());      
                this->logEndOfLine();

                this->logTimeStamp();
                this->log(&details[0]);
                this->logEndOfLine();

                this->log(std::string(60, '*'));
                this->logEndOfLine();
                this->logEndOfLine();

                returnCode = exceptionCode;

                // actions à mener lors de la découverte d'une faute
                this->faultFound();

                continueDebug = false;
            }
            break;
        // = fin du programme. Il s'agit soit la fin normale
        // soit la fin provoqué par expiration du timero
        case EXIT_PROCESS_DEBUG_EVENT:
            this->logVerbose(" (OK)");
            this->logVerboseEndOfLine();

            continueDebug = false;	
            break;  // quitter la boucle 
        }
        // Acquitter dans tous les cas, (exception ou fin de programme)
        ContinueDebugEvent(e.dwProcessId, e.dwThreadId, DBG_CONTINUE);
    }

    // arret du timer (sans effet si c'est le timer qui a provoqué l'arret du debug)
    if (_hTimer) CancelWaitableTimer(_hTimer);
    // fermeture des handles du programme débuggé
    CloseHandle(pi.hProcess); 
    CloseHandle(pi.hThread);

    // en cas d'exception levée, enregistrer l'erreur
    if (returnCode) 
    {
        // enregistrement de l'erreur dans le fichier des fautes
        // ouverture en mode "app(end)"
        std::ofstream fault(_faultFile, std::ios::app);
        fault << pNewInput->getFilePath();
        fault << " Exception n° " << std::hex << returnCode << std::dec << std::endl;
        fault.close();

        // enregistrer le code d'erreur dans l'objet
        pNewInput->setExceptionCode(returnCode);
    }

    return (returnCode);
}

// renvoie la ligne de commande complète pour l'execution de la cible en mode debug
std::string FuzzwinAlgorithm::getCmdLineDebug(const CInput *pNewInput) const
{
    return ('"' + _targetPath + "\" \"" + pNewInput->getFilePath() + '"'); 
}

void CALLBACK FuzzwinAlgorithm::timerExpired(LPVOID arg, DWORD, DWORD)
{
    HANDLE hDebugProcess = *(static_cast<PHANDLE>(arg));

    // vérification que le processus est toujours actif. si tel est le cas => destruction
    DWORD exitCode = 0;
    BOOL status = GetExitCodeProcess(hDebugProcess, &exitCode);

    if (STILL_ACTIVE == exitCode) TerminateProcess(hDebugProcess, 0); // revoir le code de fin ???
}