#include "algorithm.h"

int FuzzwinAlgorithm::sendArgumentToPintool(const std::string &command) const
{
    UINT32 commandLength = static_cast<UINT32>(command.size());
    DWORD  cbWritten = 0;

    BOOL fSuccess = WriteFile(_hPintoolPipe, 
        command.c_str(), 
        commandLength, 
        &cbWritten, 
        NULL);

    // si tout n'a pas été écrit ou erreur : le signaler
    if (!fSuccess || cbWritten != commandLength)	
    {   
        this->logTimeStamp();
        this->log("erreur envoi arguments au Pintool");
        this->logEndOfLine();
        return (EXIT_FAILURE);
    }
    else return (EXIT_SUCCESS);
}

void FuzzwinAlgorithm::callPintool() 
{
    // ligne de commande pour appel de PIN avec l'entree etudiee
    std::string cmdLine(this->getCmdLinePintool()); 
    // mise à zéro de la formule
    _formula.erase();
  
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
        BOOL fSuccess = ConnectNamedPipe(_hPintoolPipe, NULL);
        if (!fSuccess && GetLastError() != ERROR_PIPE_CONNECTED) 
        {	
            this->logTimeStamp();
            this->log("erreur de connexion au pipe FuzzWin GLE=" + std::to_string(GetLastError()));
            this->logEndOfLine();
            return; // formule vide
        }
        
        /************************************/
        /** ENVOI DES ARGUMENTS AU PINTOOL **/
        /************************************/

        int resultOfSend;
        // 0) Option ici = 'taint'
        resultOfSend = sendArgumentToPintool("taint");
        // 1) chemin vers l'entrée étudiée
        resultOfSend = sendArgumentToPintool(_pCurrentInput->getFilePath());
        // 2) nombre maximal de contraintes
        resultOfSend = sendArgumentToPintool(std::to_string(_maxConstraints));
        // 3) temps limite d'execution en secomdes
        resultOfSend = sendArgumentToPintool(std::to_string(_maxExecutionTime));
        // 4) offset des entrees à etudier
        resultOfSend = sendArgumentToPintool(_bytesToTaint);
        // 5) type d'OS hote
        resultOfSend = sendArgumentToPintool(std::to_string(_osType));

        /********************************************************/
        /** ATTENTE DE L'ARRIVEE DES DONNEES DEPUIS LE PINTOOL **/
        /********************************************************/
        char buffer[512]; // buffer de récupération des données
        DWORD cbBytesRead = 0; 

        // lecture successive de blocs de 512 octets 
        // et construction progressive de la formule
        do 
        { 
            fSuccess = ReadFile(_hPintoolPipe,  // pipe handle 
                &buffer[0],    // buffer to receive reply 
                512,            // size of buffer 
                &cbBytesRead,   // number of bytes read 
                NULL);          // not overlapped 
 
            if ( ! fSuccess && (GetLastError() != ERROR_MORE_DATA) )  break; 
            // ajout des données lues au resultat
            _formula.append(&buffer[0], cbBytesRead);

        } while (!fSuccess);  // repetition si ERROR_MORE_DATA 

        // deconnexion du pipe
        DisconnectNamedPipe(_hPintoolPipe);

        // attente de la fermeture de l'application
        WaitForSingleObject(pi.hProcess, INFINITE);
        
        // recupération du code de retour du pintool
        // (NON ENCORE IMPLEMENTE)
        DWORD exitCode = 0;
        GetExitCodeProcess(pi.hProcess, &exitCode);

        // fermeture des handles processus et thread 
        CloseHandle(pi.hProcess); 
        CloseHandle(pi.hThread);

        // si option 'keepfiles' ou 'traceonly': sauvegarde de la formule (extension .smt2)
        if (_keepFiles || _traceOnly) 
        {
            std::ofstream ofs(_pCurrentInput->getLogFile());
            ofs << infoHeader << '\n';          // entete (version pin Z3 etc)
            ofs << '\n';
            ofs << "; Fichier instrumenté : ";  // fichier d'entree etudié
            ofs << _pCurrentInput->getFileName();  
            if (_verbose) // ajout de l'arbre généalogique
            {
                CInput *pFather = _pCurrentInput->getFather();
                ofs << '(';
                while (pFather)
                {
                    ofs << " <- " << pFather->getFileName();
                    pFather = pFather->getFather();
                }
                ofs << ')';
            }
            ofs << "\n\n";
            ofs << solverConfig;    // configuration du solveur
            ofs << "\n\n";
            ofs << _formula;        // formule brute smt2
            ofs.close();
        }
    }	
    else
    {
        this->logVerboseTimeStamp();
        this->logVerbose("erreur process FuzzWin GLE=" + std::to_string(GetLastError()));
        this->logVerboseEndOfLine();
    }
}

int FuzzwinAlgorithm::createNamedPipePintool()
{
    _hPintoolPipe = CreateNamedPipe("\\\\.\\pipe\\fuzzwin",	
        PIPE_ACCESS_DUPLEX,	// accès en lecture/écriture 
        PIPE_TYPE_MESSAGE | PIPE_READMODE_MESSAGE | PIPE_WAIT, // mode message, bloquant
        1,		// une seule instance
        4096,	// buffer de sortie 
        4096,	// buffer d'entrée
        0,		// time-out du client = defaut
        NULL);	// attributs de securité par defaut

    return (INVALID_HANDLE_VALUE != _hPintoolPipe);
}

// renvoie la ligne de commande complète pour l'appel du pintool
std::string FuzzwinAlgorithm::getCmdLinePintool() const
{
    return (_cmdLinePin + '"' + _pCurrentInput->getFilePath() + '"'); 
}