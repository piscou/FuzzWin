#include "pintoolFuncs.h"

int sendArgumentsToPintool(const std::string &command)
{
    DWORD commandLength = static_cast<DWORD>(command.size());
    DWORD cbWritten = 0;

    BOOL fSuccess = WriteFile(pGlobals->hPintoolPipe, 
        command.c_str(), 
        commandLength, 
        &cbWritten, 
        NULL);

    // si tout n'a pas été écrit ou erreur : le signaler
    if (!fSuccess || cbWritten != commandLength)	
    {   
        LOG("erreur envoi arguments au Pintool\n");
        return (EXIT_FAILURE);   // erreur
    }
    else return (EXIT_SUCCESS);  // OK
}

std::string callFuzzwin(CInput* pInput) 
{
    // ligne de commande pour appel de PIN avec l'entree etudiee
    std::string cmdLine(pInput->getCmdLineFuzzwin()); 
    std::string smtFormula;
  
    STARTUPINFO si;
    PROCESS_INFORMATION pi;
    
    ZeroMemory(&si, sizeof(si));
    ZeroMemory(&pi, sizeof(pi));
    si.cb = sizeof(si);
    
    if (CreateProcess(nullptr, 
        (LPSTR) cmdLine.c_str(), 
        NULL,          // process security attributes 
        NULL,          // primary thread security attributes 
        TRUE,          // handles are inherited 
        CREATE_NO_WINDOW,    // creation flags 
        NULL,          // use parent's environment 
        NULL,          // use parent's current directory 
        &si, &pi)) 
    {          
        /***********************/
        /** CONNEXION AU PIPE **/
        /***********************/
        BOOL fSuccess = ConnectNamedPipe(pGlobals->hPintoolPipe, NULL);
        if (!fSuccess && GetLastError() != ERROR_PIPE_CONNECTED) 
        {	
            LOG("erreur de connexion au pipe FuzzWin, GLE=");
            LOG(std::to_string(GetLastError()) + '\n');
            return (smtFormula); // formule vide
        }
        
        /************************************/
        /** ENVOI DES ARGUMENTS AU PINTOOL **/
        /************************************/

        int resultOfSend;
        // 0) Option ici = 'taint'
        resultOfSend = sendArgumentsToPintool("taint");
        // 1) chemin vers l'entrée étudiée
        resultOfSend = sendArgumentsToPintool(pInput->getFilePath());
        // 2) nombre maximal de contraintes (TODO)
        resultOfSend = sendArgumentsToPintool(std::to_string(pGlobals->maxConstraints));
        // 3) temps limite d'execution en secomdes
        resultOfSend = sendArgumentsToPintool(std::to_string(pGlobals->maxExecutionTime));
        // 4) offset des entrees à etudier
        resultOfSend = sendArgumentsToPintool(pGlobals->bytesToTaint);
        // 5) type d'OS hote
        resultOfSend = sendArgumentsToPintool(std::to_string(pGlobals->osType));

        /********************************************************/
        /** ATTENTE DE L'ARRIVEE DES DONNEES DEPUIS LE PINTOOL **/
        /********************************************************/
        char buffer[512]; // buffer de récupération des données
        DWORD cbBytesRead = 0; 

        // lecture successive de blocs de 512 octets 
        // et construction progressive de la formule
        do 
        { 
            fSuccess = ReadFile( 
                pGlobals->hPintoolPipe,  // pipe handle 
                &buffer[0],    // buffer to receive reply 
                512,            // size of buffer 
                &cbBytesRead,   // number of bytes read 
                NULL);          // not overlapped 
 
            if ( ! fSuccess && (GetLastError() != ERROR_MORE_DATA) )  break; 
            // ajout des données lues au resultat
            smtFormula.append(&buffer[0], cbBytesRead);

        } while (!fSuccess);  // repetition si ERROR_MORE_DATA 

        // deconnexion du pipe
        DisconnectNamedPipe(pGlobals->hPintoolPipe);

        // attente de la fermeture de l'application
        WaitForSingleObject(pi.hProcess, INFINITE);
        
        // recupération du code de retour du pintool
        // (NON ENCORE IMPLEMENTE)
        DWORD exitCode = 0;
        GetExitCodeProcess(pi.hProcess, &exitCode);

        // fermeture des handles processus et thread 
        CloseHandle(pi.hProcess); 
        CloseHandle(pi.hThread);

        // si option 'keepfiles' : sauvegarde de la formule (extension .fzw)
        if (pGlobals->keepFiles) 
        {
            std::ofstream ofs(pInput->getLogFile());
            ofs << infoHeader;                  // entete (version pin Z3 etc)
            ofs << "; Fichier instrumenté : ";  // fichier d'entree etudié
            ofs << pInput->getFileName() << std::endl;  
            ofs << smtFormula;                  // formule brute smt2
            ofs.close();
        }
    }	
    else
    {
        VERBOSE("erreur process FuzzWin" + std::to_string(GetLastError()) + '\n');
    }
    return (smtFormula); // retour de la formule SMT2
}

int createNamedPipePintool()
{
    pGlobals->hPintoolPipe = CreateNamedPipe("\\\\.\\pipe\\fuzzwin",	
        PIPE_ACCESS_DUPLEX,	// accès en lecture/écriture 
        PIPE_TYPE_MESSAGE | PIPE_READMODE_MESSAGE | PIPE_WAIT, // mode message, bloquant
        1,		// une seule instance
        4096,	// buffer de sortie 
        4096,	// buffer d'entrée
        0,		// time-out du client = defaut
        NULL);	// attributs de securité par defaut

    return (INVALID_HANDLE_VALUE != pGlobals->hPintoolPipe);
}