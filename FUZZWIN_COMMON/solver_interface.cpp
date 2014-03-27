#include "fuzzwin_algo.h"

bool FuzzwinAlgorithm::sendToSolver(const std::string &data) const
{
    // envoi des données au solveur
    DWORD cbWritten;	
    if (!WriteFile(_hWriteToZ3, data.c_str(), (DWORD) data.size(), &cbWritten, NULL)) 
    {
       return false;
    }
    else return true;
}

bool FuzzwinAlgorithm::checkSatFromSolver() const
{
    char  bufferRead[32] = {0}; // 32 caractères => large, tres large
    DWORD nbBytesRead    = 0;
    bool  result         = false;    // par défaut pas de réponse du solveur
    
    sendToSolver("(check-sat)\n");
    Sleep(20); // pour permettre l'écriture des résultats (tricky)

    // lecture des données dans le pipe (1 seule ligne)
    BOOL fSuccess = ReadFile(_hReadFromZ3, bufferRead, 32, &nbBytesRead, NULL);
    
    if (fSuccess)  
    {
        std::string bufferString(bufferRead);
        if ("sat" == bufferString.substr(0,3)) result = true;
    }
    else
    {
        this->logTimeStamp();
        this->log("Erreur de lecture de la reponse du solveur !!");
        this->logEndOfLine();
    }
    return result;
} 

std::string FuzzwinAlgorithm::getModelFromSolver() const
{
    char bufferRead[128] = {0}; // buffer de reception des données du solveur
    std::string result;
    DWORD nbBytesRead = 0;
 
    sendToSolver("(get-model)\n");

    // lecture des données dans le pipe
    while (1)
    {
        BOOL fSuccess = ReadFile(_hReadFromZ3, bufferRead, 128, &nbBytesRead, NULL);
        if( !fSuccess) 
        {
            this->logTimeStamp();
            this->log("Erreur de lecture de la réponse du solveur !!");
            this->logEndOfLine();
            break;
        }
        else result.append(bufferRead, nbBytesRead);
        
        // si les derniers caactères sont )) alors fin du modele
        // méthode un peu 'tricky' de savoir ou cela se termine, mais ca fonctionne !!!
       std::string last6chars = result.substr(result.size() - 6, 6);
       if (")\r\n)\r\n" == last6chars) break; 
    }
    return (result);
} 

// Création du process Z3, en redirigeant ses entrées/sorties standard via des pipes
bool FuzzwinAlgorithm::createSolverProcess(const std::string &solverPath) 
{
    SECURITY_ATTRIBUTES saAttr; 
    PROCESS_INFORMATION piProcInfo; 
    STARTUPINFO			siStartInfo;
    
    // INITIALISATION DE SECURITY ATTRIBUTES
    saAttr.nLength				= sizeof(SECURITY_ATTRIBUTES); 
    saAttr.bInheritHandle		= TRUE; 
    saAttr.lpSecurityDescriptor = NULL; 

    // INITIALISATION DE PROCESSINFO
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

    // 1) handle de lecture, 2) handle d'écriture pour STDOUT de Z3. 
    // 3) handle de lecture, 4) handle d'écriture pour STDIN de Z3.
    if ( ! CreatePipe(&_hReadFromZ3, &_hZ3_stdout, &saAttr, 0) )	return false;
    if ( ! CreatePipe(&_hZ3_stdin,   &_hWriteToZ3, &saAttr, 0) )	return false;

    // Forcer le non-héritage des handles
    if ( ! SetHandleInformation(_hReadFromZ3, HANDLE_FLAG_INHERIT, 0))	return false;
    if ( ! SetHandleInformation(_hWriteToZ3,  HANDLE_FLAG_INHERIT, 0) )	return false;

    // INITIALISATION DE STARTUPINFO . 
    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO) );
    siStartInfo.cb			 = sizeof(STARTUPINFO); 
    siStartInfo.hStdError	 = _hZ3_stdout;
    siStartInfo.hStdOutput	 = _hZ3_stdout;
    siStartInfo.hStdInput	 = _hZ3_stdin;
    siStartInfo.dwFlags		|= STARTF_USESTDHANDLES;

    std::string z3CmdLine(solverPath + " /smt2 /in");
    // Creation du processus Z3
    if (!CreateProcess(NULL, (LPSTR) z3CmdLine.c_str(),     // command line 
        NULL,          // process security attributes 
        NULL,          // primary thread security attributes 
        TRUE,          // handles are inherited 
        CREATE_NO_WINDOW,    // creation flags 
        NULL,          // use parent's environment 
        NULL,          // use parent's current directory 
        &siStartInfo,  // STARTUPINFO pointer 
        &piProcInfo))  // receives PROCESS_INFORMATION 
    { 
        return false;
    }
    // sauvegarde du handle de l'exécutable
    _hZ3_process = piProcInfo.hProcess;
    _hZ3_thread  = piProcInfo.hThread;

    // configuration de Z3 (production de modeles, logique QF-BV, etc...)
    sendToSolver(solverConfig);
    return	true;	// tout s'est bien passé
}

