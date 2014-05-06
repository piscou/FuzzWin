#include "algorithm.h"

// cette fonction calcule le score d'une nouvell entrée
// via l'exécution du pintool en mode "checkscore"
void FuzzwinAlgorithm::checkScore(CInput *pNewChild)
{
    // ligne de commande pour appel de PIN avec l'entree en cours
    std::string cmdLine(this->getCmdLineCheckScore(pNewChild)); 
  
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
            return; // score nul par défaut
        }
        
        /********************************************************/
        /** ATTENTE DE L'ARRIVEE DES DONNEES DEPUIS LE PINTOOL **/
        /********************************************************/
        char buffer[32] = {0}; // buffer de récupération des données : 32 octets pour le score
        DWORD cbBytesRead = 0; 

        fSuccess = ReadFile(_hPintoolPipe,  // pipe handle 
            &buffer[0],    // buffer to receive reply 
            32,           // size of buffer 
            &cbBytesRead,   // number of bytes read 
            NULL);          // not overlapped 
 
        if (!fSuccess && GetLastError() != ERROR_PIPE_CONNECTED) 
        {	
            this->logTimeStamp();
            this->log("erreur de récupération du score GLE=" + std::to_string(GetLastError()));
            this->logEndOfLine();
            return; // score nul par défaut
        }

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

        // transformation du score char->UINT32 et affectation à l'entrée
        // un score nul signifie soit une erreur provoquée par le fichier
        // soit une erreur du pintool checkscore
        pNewChild->setScore(atoi(&buffer[0]));
    }
}

std::string FuzzwinAlgorithm::getCmdLineCheckScore(const CInput *pNewChild) const
{
    return (_cmdLineCheckScore + '"' + pNewChild->getFilePath() + '"'); 
}
