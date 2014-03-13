#include "fuzzwin_algorithm.h"

FuzzwinAlgorithm::FuzzwinAlgorithm() 
    : QObject(), _numberOfChilds(0) {}


size_t FuzzwinAlgorithm::sendNonInvertedConstraints(const std::string &formula, UINT32 bound)
{
    if (bound) 
    {
        size_t posBeginOfLine = 0; // position du début de ligne de la contrainte 'bound'
        size_t posEndOfLine   = 0; // position du fin de ligne de la contrainte 'bound'
    
        // recherche de la contrainte "bound" dans la formule
        posBeginOfLine	= formula.find("(assert (= C_" + std::to_string((_Longlong) bound));
        // recherche de la fin de la ligne
        posEndOfLine	= formula.find_first_of('\n', posBeginOfLine);
        // extraction des contraintes non inversées et envoi au solveur
        sendToSolver(formula.substr(0, posEndOfLine + 1));
        return (posEndOfLine); // position de la fin de la dernière contrainte dans la formule
    }
    else return (0);
}

// renvoie l'inverse de la contrainte fournie en argument
// la contrainte originale (argument fourni) reste inchangée
std::string FuzzwinAlgorithm::invertConstraint(const std::string &constraint) 
{
    // copie de la contrainte
    std::string invertedConstraint(constraint);
    size_t pos = invertedConstraint.find("true");
    
    if (pos != std::string::npos)  // 'true'  -> 'false' 
    {
        invertedConstraint.replace(pos, 4, "false");   
    }
    else  // 'false' -> 'true'
    {
        invertedConstraint.replace(invertedConstraint.find("false"), 5, "true");  
    }
    return (invertedConstraint);
}

ListOfInputs FuzzwinAlgorithm::expandExecution(CInput *pInput, HashTable &h, UINT32 *nbFautes) 
{  
    ListOfInputs result;	                // liste de nouveaux objets de type CInput générées
    UINT32	bound = pInput->getBound();     // bound du fichier actuellement étudié
    size_t pos = 0, posLastConstraint = 0;  // indexs de position dans une chaine de caractères
    
    std::string formula;                // formule fournie en sortie par le pintool
    std::string inputContent;           // contenu du fichier étudié
    std::string	constraintJ;	        // partie de formule associée à la contrainte J
    std::string constraintJ_inverted;   // la même contrainte, inversée

    /********************************************************/
    /** Execution du pintool et récupération de la formule **/
    /********************************************************/
    formula = callFuzzwin(pInput);
    if (formula.empty())
    {
        emit sendToGuiVerbose("\tAucune formule recue du pintool !!\n");
        return result; // aucune formule ou erreur
    }

    // récupération du nombre de contraintes dans la formule
    pos = formula.find_last_of('@');
    if (std::string::npos == pos) return result;
    UINT32 nbContraintes = std::stoi(formula.substr(pos + 1));

    // si le "bound" est supérieur aux nombre de contraintes => aucune nouvelle entrée, retour
    if (bound >= nbContraintes) 	
    {
        VERBOSE("\tPas de nouvelles contraintes inversibles\n");
        return result;
    }
    
    /********************************************/
    /** Traitement et résolution de la formule **/
    /********************************************/

    // les contraintes de 0 à bound ne seront pas inversées => les envoyer au solveur
    // en retour, un index pointant vers la fin de la dernière contrainte envoyée
    posLastConstraint = sendNonInvertedConstraints(formula, bound);
    
    // récupération du contenu du fichier cible étudié
    inputContent = pInput->getFileContent(); 

    // => boucle sur les contraintes de "bound + 1" à "nbContraintes" inversées et resolues successivement
    for (UINT32 j = bound + 1 ; j <= nbContraintes ; ++j) 
    {	
        VERBOSE("\tinversion contrainte " + std::to_string(j));
            
        // recherche de la prochaine contrainte dans la formule, à partir de la position de la précédente contrainte 
        pos = formula.find("(assert (=", posLastConstraint);          
        // envoi au solveur de toutes les déclarations avant la contrainte
        sendToSolver(formula.substr(posLastConstraint, (pos - posLastConstraint)));
        // envoi au solveur de la commande "push 1"
        // reserve une place sur la pile pour la prochaine déclaration (la contrainte inversée)
        sendToSolver("(push 1)\n");

        // recherche de la fin de la ligne de la contrainte actuelle (et future précédente contrainte)
        posLastConstraint    = formula.find_first_of('\n', pos);     
        // extraction de la contrainte, et inversion
        constraintJ          = formula.substr(pos, (posLastConstraint - pos));
        constraintJ_inverted = invertConstraint(constraintJ);    

        // envoi de la contrainte J inversée au solveur, et recherche de la solution
        sendToSolver(constraintJ_inverted + '\n');

        if (checkSatFromSolver())	// SOLUTION TROUVEE : DEMANDER LES RESULTATS
        {							
            std::string newInputContent(inputContent); // copie du contenu du fichier initial
            std::string solutions;

            // récupération des solutions du solveur
            solutions = getModelFromSolver();
                
            // modification des octets concernés dans le contenu du nouveau fichier
            int tokens[2] = {1, 2};
            std::sregex_token_iterator it (solutions.begin(), solutions.end(), pGlobals->regexModel, tokens);
            std::sregex_token_iterator end;
            while (it != end) 
            {
                int offset = std::stoi(it->str(), nullptr, 10); ++it; // 1ere valeur = offset
                int value =  std::stoi(it->str(), nullptr, 16); ++it; // 2eme valeur = valeur
                newInputContent[offset] = static_cast<char>(value);
            }

            // calcul du hash du nouveau contenu et insertion dans la table de hachage. 
            // Si duplicat (retour 'false'), ne pas créer le fichier
            auto insertResult = h.insert(pGlobals->fileHash(newInputContent));
            if (insertResult.second != false)
            {
                // fabrication du nouvel objet "fils" à partir du père
                CInput *newChild = new CInput(pInput, ++_numberOfChilds, j);

                // création du fichier et insertion du contenu modifié
                std::ofstream newFile(newChild->getFileInfo(), std::ios::binary);
                newFile.write(newInputContent.c_str(), newInputContent.size());
                newFile.close();

                VERBOSE("-> nouveau fichier " + newChild->getFileName());

                // test du fichier de suite; si retour nul le fichier est valide, donc l'insérer dans la liste
                DWORD checkError = debugTarget(newChild);
                if (!checkError) result.push_back(newChild);
                else ++*nbFautes;
            }	
            // le fichier a déjà été généré (hash présent ou ... collision)
            else VERBOSE("-> deja généré\n");
        }
        // pas de solution trouvée par le solveur
        else VERBOSE(" : aucune solution\n");   
       
        // enlever la contrainte inversée de la pile du solveur, et remettre l'originale
        sendToSolver("(pop 1)\n" + constraintJ + '\n');
    } // end for
       
    // effacement de toutes les formules pour laisser une pile vierge
    // pour le prochain fichier d'entrée qui sera testé
    sendToSolver("(reset)\n");

    return (result);
}


UINT32 FuzzwinAlgorithm::algorithmeSearch() 
{
    ListOfInputs workList;		// liste des fichiers à traiter 
    HashTable	 hashTable;		// table de hachage des fichiers déjà traités, pour éviter les doublons
    CInput*		 pFirstInput;	// objet représentant l'entrée initiale
    UINT32		 nbFautes = 0;	// nombre de fautes trouvées au cours de l'analyse
    
    // création de l'objet représentant l'entrée initiale
    QString firstFilePath(QString::fromLocal8Bit(pGlobals->firstInputPath.c_str()));
    pFirstInput = new CInput(firstFilePath);
 
    // calcul du hash de la première entrée, et insertion dans la liste des hashes
    hashTable.insert(pGlobals->fileHash(pFirstInput->getFileContent()));

    // initialisation de la liste de travail avec la première entrée
    workList.push_back(pFirstInput);

    /**********************/
    /** BOUCLE PRINCIPALE */
    /**********************/
    while ( !workList.empty() ) 
    {
        LOG("[" + std::to_string(workList.size()) + "] ELEMENTS DANS LA WORKLIST\n");
        
        // tri des entrées selon leur score (si option activée)
        if (pGlobals->computeScore) workList.sort(sortInputs);

        // récupération et retrait du fichier ayant le meilleur score (dernier de la liste)
        CInput* pCurrentInput = workList.back();
        workList.pop_back();

        LOG("[!] exécution de " + pCurrentInput->getFileName());
        
        VERBOSE(" (bound = " + std::to_string(pCurrentInput->getBound()) + ')');
        if (pGlobals->computeScore)
        {
            VERBOSE(" (score = " + std::to_string(pCurrentInput->getScore()) + ')');
        }
        if (pCurrentInput->parent()) 
        {
            VERBOSE(" (père = " + pCurrentInput->getFather()->getFileName() + ')');
        }

        LOG("\n");

        // exécution de PIN avec cette entrée (fonction ExpandExecution)
        // et recupération d'une liste de fichiers dérivés
        // la table de hachage permet d'écarter les doublons déjà générés
        auto childInputs = expandExecution(pCurrentInput, hashTable, &nbFautes);

        if (!childInputs.size())  LOG("\t pas de nouveaux fichiers\n")  
        else   LOG("\t " + std::to_string(childInputs.size()) + " nouveau(x) fichier(s)\n");

        // insertion des fichiers dans la liste
        workList.insert(workList.cbegin(), childInputs.cbegin(), childInputs.cend());

       // effacement de l'objet si pas d'enfant et s'il est "sain"
        if (!pCurrentInput->getExceptionCode() && !pCurrentInput->childCount())
        {
            delete (pCurrentInput);
        }
    }
    return (nbFautes);
}

DWORD WINAPI FuzzwinAlgorithm::timerThread(LPVOID lpParam)
{
    // handle du processus à monitorer, passé en argument
    HANDLE hProcess = reinterpret_cast<HANDLE>(lpParam);

    // Attente du temps imparti, ou du signal envoyé par le thread principal
    // si timeout atteint, terminer le processus de debuggage
    DWORD result = WaitForSingleObject(_hTimoutEvent, (DWORD) (pGlobals->maxExecutionTime * 1000));

    if (WAIT_TIMEOUT == result) TerminateProcess(hProcess, 0);    // revoir le code de fin ???
  
    return (result);
}

// cette fonction teste si l'entrée fait planter le programme
DWORD FuzzwinAlgorithm::debugTarget(CInput *pInput) 
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
        _hTimerThread = CreateThread(
            nullptr, // attributs de sécurité par défaut
            0,       // taille de pile par defaut
            this->timerThread,  // nom de la fonction du thread
            pi.hProcess,    // argument à transmettre : le handle du processus surveillé
            0,              // attributs de creation par défaut
            nullptr);       // pas besoin du threadId de ce thread

        // création de l'évenement de fin de debuggage à cause du temps
        _hTimoutEvent = CreateEvent( 
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
                UINT64 exceptionAddress = (UINT64) e.u.Exception.ExceptionRecord.ExceptionAddress;
                QString adressInHex = QString("%1").arg(exceptionAddress, 0, 16);
                
                LOG("\n\t-------------------------------------------------\n");
                LOG("\t@@@ EXCEPTION @@@ Fichier " + pInput->getFileName());
                LOG("\n\tAdresse 0x" + qPrintable(adressInHex));
                LOG(" code " + std::to_string(exceptionCode));
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
    SetEvent(_hTimoutEvent);
    // fermeture des handles du programme débuggé
    CloseHandle(pi.hProcess); 
    CloseHandle(pi.hThread);
    // fermeture du handle du thread "gardien du temps"
    if (pGlobals->maxExecutionTime) CloseHandle(_hTimerThread);

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



void FuzzwinAlgorithm::launch() 
{
    
    /********************************************/
    /** création du tube nommé avec le Pintool **/
    /********************************************/
    if (!createNamedPipePintool())
    {
        this->sendToLogWindow ("Erreur de création du pipe fuzzWin");
    }
    else VERBOSE("Pipe Fuzzwin OK");
    
    /**********************************************************/
    /** création du process Z3 avec redirection stdin/stdout **/ 
    /**********************************************************/
    if (!createSolverProcess(convertQStringToString(_z3Path)))
    {
        this->sendToLogWindow ("erreur création processus Z3");
    }
    else VERBOSE("Process Z3 OK");
    
    
    UINT32 nbFautes = algorithmeSearch();

    LOG("\n******************************\n");
    LOG("* ---> FIN DE L'ANALYSE <--- *\n");
    LOG("******************************\n");

    if (nbFautes) // si une faute a été trouvée
    { 
        LOG("---> " + std::to_string(nbFautes) + " faute" + ((nbFautes > 1) ? "s " : " "));
        LOG("!! consultez le fichier fault.txt <---\n");
    }
    else LOG("* aucune faute... *\n");
}


bool sendToSolver(const std::string &data) 
{
    // envoi des données au solveur
    DWORD cbWritten;	
    if (!WriteFile(pGlobals->hWriteToZ3, data.c_str(), (DWORD) data.size(), &cbWritten, NULL)) 
    {
       return false;
    }
    else return true;
}

bool checkSatFromSolver()
{
    char bufferRead[32] = {0}; // 32 caractères => large, tres large
    DWORD nbBytesRead = 0;
    bool result = false;    // par défaut pas de réponse du solveur
    
    sendToSolver("(check-sat)\n");
    Sleep(10);

    // lecture des données dans le pipe (1 seule ligne)
    BOOL fSuccess = ReadFile(pGlobals->hReadFromZ3, bufferRead, 32, &nbBytesRead, NULL);
    
    if (!fSuccess)  LOG("erreur de lecture de la reponse du solveur\n")
    else 
    {
        std::string bufferString(bufferRead);
        if ("sat" == bufferString.substr(0,3)) result = true;
    }

    return result;
} 

std::string getModelFromSolver()
{
    char bufferRead[BUFFER_SIZE] = {0}; // buffer de reception des données du solveur
    std::string result;
    DWORD nbBytesRead = 0;
 
    sendToSolver("(get-model)\n");

    // lecture des données dans le pipe
    while (1)
    {
        BOOL fSuccess = ReadFile(pGlobals->hReadFromZ3, bufferRead, BUFFER_SIZE, &nbBytesRead, NULL);
        if( !fSuccess) 
        {
            LOG("erreur de lecture de la réponse du solveur\n");
            break;
        }
        else result.append(bufferRead, nbBytesRead);
        
        // si les derniers caactères sont )) alors fin du modele
        // méthode un peu 'tricky' de savoir ou cela se termine, mais ca fonctionne !!!
       std::string last6chars = result.substr(result.size() - 6, 6);
       if (")\r\n)\r\n" == last6chars) break; 
    }
    return result;
} 


// Creaation du process Z3, en redirigeant ses entrées/sorties standard via des pipes
bool createSolverProcess(const std::string &solverPath) 
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
    if ( ! CreatePipe(&pGlobals->hReadFromZ3, &pGlobals->hZ3_stdout, &saAttr, 0) )	return false;
    if ( ! CreatePipe(&pGlobals->hZ3_stdin, &pGlobals->hWriteToZ3, &saAttr, 0) )	return false;

    // Forcer le non-héritage des handles
    if ( ! SetHandleInformation(pGlobals->hReadFromZ3, HANDLE_FLAG_INHERIT, 0))	return false;
    if ( ! SetHandleInformation(pGlobals->hWriteToZ3, HANDLE_FLAG_INHERIT, 0) )	return false;

    // INITIALISATION DE STARTUPINFO . 
    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO) );
    siStartInfo.cb			 = sizeof(STARTUPINFO); 
    siStartInfo.hStdError	 = pGlobals->hZ3_stdout;
    siStartInfo.hStdOutput	 = pGlobals->hZ3_stdout;
    siStartInfo.hStdInput	 = pGlobals->hZ3_stdin;
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
    pGlobals->hZ3_process = piProcInfo.hProcess;
    pGlobals->hZ3_thread  = piProcInfo.hThread;

    // configuration de Z3 (production de modeles, logique QF-BV, etc...)
    sendToSolver(solverConfig);
    return	true;	// tout s'est bien passé
}
