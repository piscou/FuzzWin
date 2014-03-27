#include "fuzzwin_algorithm.h"

/*********************/
/*** Classe CInput ***/
/*********************/

// création du 'nb' nouvel objet dérivé de l'objet 'pFather' à la contrainte 'b'
CInput::CInput(CInput* pFather, quint32 nb, quint32 b) : QTreeWidgetItem(pFather),
    _bound(b), 
    _exceptionCode(0),
    _score(0)
{ 	
    // construction du chemin de fichier à partir de celui du père
    // nom du dossier + nouveau nom de fichier
    _fileInfo = pFather->getFileInfo().absolutePath() + QString("/input%1").arg(nb);
}

// constructeur spécifique 1ere entrée
CInput::CInput(const QString &firstInputPath) : QTreeWidgetItem(),
       _bound(0), 
       _exceptionCode(0), 
       _score(0),
       _fileInfo(firstInputPath)  {}

CInput::~CInput() {}

quint32	  CInput::getBound() const         { return this->_bound; }
quint32	  CInput::getScore() const         { return this->_score; }
quint32	  CInput::getExceptionCode() const { return this->_exceptionCode; }
quint32   CInput::getFileSize() const  { return static_cast<quint32>(_fileInfo.size()); }
QFileInfo CInput::getFileInfo() const 	   { return this->_fileInfo; }

// renvoie le chemin du fichier concerné (format std::string)
std::string CInput::getFilePath() const
{
    return (qPrintable(QDir::toNativeSeparators(_fileInfo.absoluteFilePath())));
}

// renvoie le chemin vers le fichier qui contiendra la formule SMT2
// associée à l'execution de cette entrée (option --keepfiles mise à TRUE)
QString CInput::getLogFilePath() const 
{
    return (_fileInfo.absoluteFilePath() + ".fzw");
}

// renvoie le contenu du fichier sous la forme de string
std::string CInput::getFileContent() const
{
    QFile file(_fileInfo.absoluteFilePath());
        
    quint32 fileSize = static_cast<quint32>(file.size());

    file.open(QIODevice::ReadOnly);
    QByteArray content = file.read(file.size());

    return (std::string(content, content.size()));    
}

// numéro de contrainte inversée qui a donné naissance à cette entrée
void CInput::setBound(const quint32 b)	      { this->_bound = b; }
// Affectation d'un score à cette entrée
void CInput::setScore(const quint32 s)	      { this->_score = s; }
// numéro d'Exception généré par cette entrée
void CInput::setExceptionCode(const quint32 e) { this->_exceptionCode = e; }

/*******************************/
/*** Classe FuzzwinAlgorithm ***/
/*******************************/

FuzzwinAlgorithm::FuzzwinAlgorithm(const QString &firstInputPath, const QString &targetPath, const QString &resultsDir, quint32 maxtime) 
    : QObject(), 
    _numberOfChilds(0), 
    _nbFautes(0),
    _regexModel(parseZ3ResultRegex, std::regex::ECMAScript),
    _hash(QCryptographicHash::Md5),
    _resultDir(resultsDir),
    _targetPath(qPrintable(targetPath))
{
    // copie du fichier initial dans le dossier de résultat (sans extension, avec le nom 'input0')
    QFile::copy(firstInputPath, resultsDir + "/input0");
    // construction de la première entrée de la liste de travail
    _currentInput = new CInput(resultsDir + "/input0");   

    // calcul de son hash et insertion dans la liste
    QFile firstFile(firstInputPath);
    _hash.reset();
    _hash.addData(&firstFile);
    _hashTable.insert(_hash.result().toHex());

    // chemin prérempli pour le fichier de fautes (non créé pour l'instant)
    _faultFile = resultsDir + "/fault.txt";

    if (maxtime)
    {
        _maxExecutionTime = maxtime;
        // préparation du timer pour la partie debug
        _pOutOfTimeDebug = new QTimer;
        _pOutOfTimeDebug->setSingleShot(true); // 1 seul décompte à la fois
        _pOutOfTimeDebug->setInterval(1000*_maxExecutionTime);
        connect(_pOutOfTimeDebug, SIGNAL(timeout()), this, SLOT(outOfTimeDebug()));
    }
    else
    {
        _pOutOfTimeDebug = nullptr; 
        _maxExecutionTime = 0;
    }
}

// destructeur : fermeture des handles
FuzzwinAlgorithm::~FuzzwinAlgorithm()
{
// fermeture du processus Z3
    CloseHandle(_hZ3_process); 
    CloseHandle(_hZ3_thread);
    // fermeture des différents tubes de communication avec Z3
    CloseHandle(_hZ3_stdout); 	
    CloseHandle(_hZ3_stdin);
    CloseHandle(_hReadFromZ3);	
    CloseHandle(_hWriteToZ3);
    // fermeture des tubes nommés avec le pintool Fuzzwin
    CloseHandle(_hPintoolPipe);

    // fermeture du timer
    delete (_pOutOfTimeDebug);
}


quint32 FuzzwinAlgorithm::sendNonInvertedConstraints(quint32 bound)
{
    if (bound) 
    {
        quint32 posBeginOfLine = 0; // position du début de ligne de la contrainte 'bound'
        quint32 posEndOfLine   = 0; // position du fin de ligne de la contrainte 'bound'
    
        // recherche de la contrainte "bound" dans la formule
        posBeginOfLine	= _formula.find("(assert (= C_" + std::to_string((_Longlong) bound));
        // recherche de la fin de la ligne
        posEndOfLine	= _formula.find_first_of('\n', posBeginOfLine);
        // extraction des contraintes non inversées et envoi au solveur
        sendToSolver(_formula.substr(0, posEndOfLine + 1));
        return (static_cast<quint32>(posEndOfLine)); // position de la fin de la dernière contrainte dans la formule
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

ListOfInputs FuzzwinAlgorithm::expandExecution() 
{  
    ListOfInputs result;	                 // liste de nouveaux objets de type CInput générées
    quint32	     bound = _currentInput->getBound(); // bound du fichier actuellement étudié
    quint32      pos = 0;
    quint32      posLastConstraint = 0;      // indexes de position dans une chaine de caractères
    
    std::string  inputContent;           // contenu du fichier étudié
    std::string	 constraintJ;	        // partie de formule associée à la contrainte J
    std::string  constraintJ_inverted;   // la même contrainte, inversée

    QString      logMsg; // uniquement en mode verbose

    /********************************************************/
    /** Execution du pintool et récupération de la formule **/
    /********************************************************/
    callFuzzwin(); // formule inscrite dans la variable membre
    if (_formula.empty())
    {
        emit sendToGuiVerbose("Aucune formule recue du pintool !!\n");
        return result; // aucune formule ou erreur
    }

    // récupération du nombre de contraintes dans la formule
    pos = _formula.find_last_of('@');
    if (std::string::npos == pos) return result;
    quint32 nbContraintes = std::stoi(_formula.substr(pos + 1));

    emit sendToGuiVerbose(QString("  %1 contraintes extraites\n").arg(nbContraintes));

    // si le "bound" est supérieur aux nombre de contraintes => aucune nouvelle entrée, retour
    if (bound >= nbContraintes) 	
    {
        emit sendToGuiVerbose("  Pas de nouvelles contraintes inversibles\n");
        return result;
    }
    
    /********************************************/
    /** Traitement et résolution de la formule **/
    /********************************************/

    // les contraintes de 0 à bound ne seront pas inversées => les envoyer au solveur
    // en retour, un index pointant vers la fin de la dernière contrainte envoyée
    posLastConstraint = sendNonInvertedConstraints(bound);
    
    // récupération du contenu du fichier cible étudié
    inputContent = _currentInput->getFileContent(); 

    // => boucle sur les contraintes de "bound + 1" à "nbContraintes" inversées et resolues successivement
    for (quint32 j = bound + 1 ; j <= nbContraintes ; ++j) 
    {	
        logMsg = QString(" -> inversion contrainte %1").arg(j);
            
        // recherche de la prochaine contrainte dans la formule, à partir de la position de la précédente contrainte 
        pos = _formula.find("(assert (=", posLastConstraint);          
        // envoi au solveur de toutes les déclarations avant la contrainte
        sendToSolver(_formula.substr(posLastConstraint, (pos - posLastConstraint)));
        // envoi au solveur de la commande "push 1"
        // reserve une place sur la pile pour la prochaine déclaration (la contrainte inversée)
        sendToSolver("(push 1)\n");

        // recherche de la fin de la ligne de la contrainte actuelle (et future précédente contrainte)
        posLastConstraint    = _formula.find_first_of('\n', pos);     
        // extraction de la contrainte, et inversion
        constraintJ          = _formula.substr(pos, (posLastConstraint - pos));
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
            std::sregex_token_iterator it (solutions.begin(), solutions.end(), _regexModel, tokens);
            std::sregex_token_iterator end;
            while (it != end) 
            {
                int offset = std::stoi(it->str(), nullptr, 10); ++it; // 1ere valeur = offset
                int value =  std::stoi(it->str(), nullptr, 16); ++it; // 2eme valeur = valeur
                newInputContent[offset] = static_cast<char>(value);
            }

            // calcul du hash du nouveau contenu et insertion dans la table de hachage. 
            // Si duplicat (retour 'false'), ne pas créer le fichier
            _hash.reset();
            _hash.addData(newInputContent.c_str(), newInputContent.size());
            QByteArray insertResult = _hash.result().toHex();
            HashTable::const_iterator resultFind = _hashTable.find(insertResult);
            if (resultFind == _hashTable.constEnd()) // entrée non trouvée => nouvel élément
            {
                // insertion du hash
                _hashTable.insert(insertResult);

                // fabrication du nouvel objet "fils" à partir du père
                CInput *newChild = new CInput(_currentInput, ++_numberOfChilds, j);

                // création du fichier et insertion du contenu modifié
                QFile newFile(newChild->getFileInfo().absoluteFilePath());
                newFile.open(QIODevice::WriteOnly);
                newFile.write(newInputContent.c_str(), newInputContent.size());
                newFile.close();

                logMsg += QString(" -> nouveau fichier %1").arg(newChild->getFileInfo().fileName());

                // test du fichier de suite; si retour nul le fichier est valide, donc l'insérer dans la liste
                DWORD checkError = debugTarget(newChild);
                if (!checkError)  result.push_back(newChild);
                else ++_nbFautes;
                
                emit newInput(*newChild);
            }	
            // le fichier a déjà été généré (hash présent ou ... collision)
            else logMsg += "-> deja généré\n";
        }
        // pas de solution trouvée par le solveur
        else emit sendToGuiVerbose(logMsg + " : aucune solution\n");   

        // enlever la contrainte inversée de la pile du solveur, et remettre l'originale
        sendToSolver("(pop 1)\n" + constraintJ + '\n');
    } // end for
       
    // effacement de toutes les formules pour laisser une pile vierge
    // pour le prochain fichier d'entrée qui sera testé
    sendToSolver("(reset)\n");

    return (result);
}

void FuzzwinAlgorithm::algorithmSearch() 
{
    // création du tube nommé avec le Pintool
    if (!createNamedPipePintool())
    {
        emit sendToGui(TIMESTAMP + TEXTRED("Erreur de création du pipe fuzzWin") + LINEFEED);
        return;
    }
    else emit sendToGuiVerbose(TIMESTAMP + TEXTGREEN("Pipe Fuzzwin OK") + LINEFEED);
    
    // création du process Z3 avec redirection stdin/stdout **/ 
    if (!createSolverProcess(_z3Path))
    {  
        emit sendToGui(TIMESTAMP + TEXTRED("erreur création processus Z3") + LINEFEED);
        return;
    }
    else emit sendToGuiVerbose(TIMESTAMP + TEXTGREEN("Process Z3 OK") + LINEFEED);
    
    // initialisation de la liste de travail avec la première entrée
    ListOfInputs workList;
    workList += _currentInput;
    QString logMessage;

    /**********************/
    /** BOUCLE PRINCIPALE */
    /**********************/
    while ( !workList.empty() ) 
    {
        emit sendToGui(TIMESTAMP + QString("[%1] ELEMENTS DANS LA WORKLIST\n").arg(workList.size()) + LINEFEED);
        
        // tri des entrées selon leur score (si option activée)
        if (_computeScore) qSort(workList.begin(), workList.end(), sortCInputs);

        // récupération et retrait du fichier ayant le meilleur score (dernier de la liste)
        _currentInput = workList.back();
        workList.pop_back();

        logMessage = QString("[!] exécution de %1").arg(_currentInput->getFileInfo().fileName());
        if (_verbose)
        {
            logMessage += QString(" (bound = %1").arg(_currentInput->getBound());
            if (_computeScore)
            {
                logMessage += QString(" (score = %1)").arg(_currentInput->getScore());
            }
            logMessage += ')';
        }
        emit sendToGui(logMessage + LINEFEED);

        // exécution de PIN avec cette entrée (fonction ExpandExecution)
        // et recupération d'une liste de fichiers dérivés
        // la table de hachage permet d'écarter les doublons déjà générés
        ListOfInputs childInputs = expandExecution();

        // vérification de la présence de nouveaux fichiers, via la taille de la liste
        quint32 listSize = childInputs.size();
        if (listSize) emit sendToGui(QString(" -> %1 nouveau(x) fichier(s)").arg(listSize));
        else          emit sendToGui(" -> pas de nouveaux fichiers");
        emit sendToGui(LINEFEED);

        // insertion des fichiers dans la liste
        workList += childInputs;

       // effacement de l'objet si pas d'enfant et s'il est "sain"
        if (_currentInput->getExceptionCode() && !_currentInput->childCount())
        {
            // si pas d'option 'keepfiles' effacer physiquement le fichier
            if (!_keepFiles) QFile::remove(toQString(_currentInput->getFilePath()));
            delete (_currentInput);
        }
    }
    // fin de l'algorithme : envoi des données à la GUI
    emit sendNbFautes(_nbFautes);
}

void FuzzwinAlgorithm::outOfTimeDebug()
{
    // vérification que le processus est toujours actif. si tel est le cas => destruction
    DWORD exitCode = 0;
    BOOL status = GetExitCodeProcess(_hDebugProcess, &exitCode);

    if (STILL_ACTIVE == exitCode) TerminateProcess(_hDebugProcess, 0);    // revoir le code de fin ???
}

// cette fonction teste si l'entrée fait planter le programme
DWORD FuzzwinAlgorithm::debugTarget(CInput *newInput) 
{
    // Execution de la cible en mode debug pour récupérer la cause et l'emplacement de l'erreur
    STARTUPINFO         si; 
    PROCESS_INFORMATION pi;
    DEBUG_EVENT         e;
    
    ZeroMemory(&si, sizeof(si));
    ZeroMemory(&pi, sizeof(pi));
    ZeroMemory(&e,  sizeof(e));
    si.cb = sizeof(si);
    
    std::string cmdLineDebug(getCmdLineDebug(newInput));	
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
        int gle = GetLastError();
        emit sendToGuiVerbose(TIMESTAMP + TEXTRED("erreur createProcess Debug") + LINEFEED);
        return 0; // fin de la procédure prématurément
    }
    // stockage du handle du processus
    _hDebugProcess = pi.hProcess;

    // timer pour stopper le debuggage au bout du temps spécifié
    if (_maxExecutionTime) _pOutOfTimeDebug->start();

    /**********************/
    /* DEBUT DU DEBUGGAGE */
    /**********************/
    while (continueDebug)	
    {
        // si erreur dans le debuggage : tout stopper et quitter la boucle
        if (!WaitForDebugEvent(&e, INFINITE)) 
        {
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
                
                emit sendToGui(TIMESTAMP + "-----------------------------------" + LINEFEED);
                emit sendToGui(QString("@@@ EXCEPTION @@@ Fichier %1\n").arg(newInput->getFileInfo().fileName()) + LINEFEED);
                emit sendToGui(QString("Adresse 0x%1").arg(exceptionAddress, 0, 16));
                emit sendToGui(QString(" code %1").arg(exceptionCode, 0, 16) + LINEFEED);
                emit sendToGui(TIMESTAMP + "-----------------------------------" + LINEFEED);
                returnCode = exceptionCode;
                continueDebug = false;
            }
            break;
        // = fin du programme. Il s'agit soit la fin normale
        // soit la fin provoqué par le thread "gardien du temps"
        case EXIT_PROCESS_DEBUG_EVENT:
            emit sendToGuiVerbose(" - no crash ;(" + LINEFEED);
            continueDebug = false;	
            // fermeture du timer, si toujours actif
            if (_maxExecutionTime)
            {
                if (!_pOutOfTimeDebug->isActive()) 
                {
                    emit sendToGuiVerbose("out of time" + LINEFEED);
                    _pOutOfTimeDebug->stop();
                }
            }
            // quitter la boucle 
            break;
        }
        // Acquitter dans tous les cas, (exception ou fin de programme)
        ContinueDebugEvent(e.dwProcessId, e.dwThreadId, DBG_CONTINUE);
    }

    // fermeture des handles du programme débuggé
    CloseHandle(pi.hProcess); 
    CloseHandle(pi.hThread);


    // en cas d'exception levée, enregistrer l'erreur
    if (returnCode) 
    {
        // enregistrement de l'erreur dans le fichier des fautes, ouvert en mode "append"
        QFile faultFile(_faultFile);
        faultFile.open(QIODevice::Append | QIODevice::Text);
        QTextStream fault(&faultFile);
        fault << _faultFile << QString(" Exception n°%1\n").arg(returnCode, 0, 16);
        faultFile.close();

        // enregistrer le code d'erreur dans l'objet
        _currentInput->setExceptionCode(returnCode);
    }

    return (returnCode);
}

int FuzzwinAlgorithm::sendArgumentsToPintool(const std::string &command)
{
    DWORD commandLength = static_cast<DWORD>(command.size());
    DWORD cbWritten     = 0;

    BOOL fSuccess = WriteFile(_hPintoolPipe, 
        command.c_str(), 
        commandLength, 
        &cbWritten, 
        NULL);

    // si tout n'a pas été écrit ou erreur : le signaler
    if (!fSuccess || (cbWritten != commandLength))	
    {   
        emit sendToGui("erreur envoi arguments au Pintool\n");
        return (EXIT_FAILURE);   // erreur
    }
    else return (EXIT_SUCCESS);  // OK
}

void FuzzwinAlgorithm::callFuzzwin() 
{
    // ligne de commande pour appel de PIN avec l'entree etudiee
    std::string cmdLine(getCmdLineFuzzwin()); 
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
            emit sendToGui(QString("erreur de connexion au pipe FuzzWin, GLE=%1\n").arg(GetLastError()));
        }
        
        /************************************/
        /** ENVOI DES ARGUMENTS AU PINTOOL **/
        /************************************/

        int resultOfSend;
        // 0) Option ici = 'taint'
        resultOfSend = sendArgumentsToPintool("taint");
        // 1) chemin vers l'entrée étudiée
        resultOfSend = sendArgumentsToPintool(_currentInput->getFilePath());
        // 2) nombre maximal de contraintes (TODO)
        resultOfSend = sendArgumentsToPintool(std::to_string(_maxConstraints));
        // 3) temps limite d'execution en secomdes
        resultOfSend = sendArgumentsToPintool(std::to_string(_maxExecutionTime));
        // 4) offset des entrees à etudier
        resultOfSend = sendArgumentsToPintool(_bytesToTaint);
        // 5) type d'OS hote
        resultOfSend = sendArgumentsToPintool(std::to_string(_osType));

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
                &buffer[0],     // buffer to receive reply 
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

        // si option 'keepfiles' : sauvegarde de la formule (extension .fzw)
        if (_keepFiles) 
        {
            QFile formulaFile(_currentInput->getLogFilePath());
            formulaFile.open(QIODevice::WriteOnly | QIODevice::Text);
            QTextStream formulaStream(&formulaFile);
            formulaStream << infoHeader.c_str();         // entete (version pin Z3 etc)
            formulaStream << QString("; Fichier instrumenté : %1\n").arg(_currentInput->getFileInfo().fileName()); // fichier d'entree etudié
            formulaStream <<  _formula.c_str();       // formule brute smt2
            formulaFile.close();
        }
    }	
    else emit sendToGuiVerbose(QString("erreur process FuzzWin GLE=%1\n").arg(GetLastError()));
}

bool FuzzwinAlgorithm::sendToSolver(const std::string &data) 
{
    // envoi des données au solveur
    DWORD cbWritten;	
    if (!WriteFile(_hWriteToZ3, data.c_str(), (DWORD) data.size(), &cbWritten, NULL)) 
    {
       return false;
    }
    else return true;
}

bool FuzzwinAlgorithm::checkSatFromSolver()
{
    char bufferRead[32] = {0}; // 32 caractères => large, tres large
    DWORD nbBytesRead = 0;
    bool result = false;    // par défaut pas de réponse du solveur
    
    sendToSolver("(check-sat)\n");
    Sleep(10); // pour permettre l'écriture des résultats (tricky)

    // lecture des données dans le pipe (1 seule ligne)
    BOOL fSuccess = ReadFile(_hReadFromZ3, bufferRead, 32, &nbBytesRead, NULL);
    
    if (fSuccess)  
    {
        std::string bufferString(bufferRead);
        if ("sat" == bufferString.substr(0,3)) result = true;
    }
    else emit sendToGui(TIMESTAMP + TEXTRED("erreur de lecture de la reponse du solveur\n") + LINEFEED);

    return result;
} 

std::string FuzzwinAlgorithm::getModelFromSolver()
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
            emit sendToGui("erreur de lecture de la réponse du solveur\n");
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
std::string FuzzwinAlgorithm::getCmdLineFuzzwin() const
{
    std::string filePath = qPrintable(QDir::toNativeSeparators(_currentInput->getFileInfo().absoluteFilePath()));
    return (_cmdLinePin + '"' + filePath + '"'); 
}

// renvoie la ligne de commande complète pour l'execution de la cible en mode debug
std::string FuzzwinAlgorithm::getCmdLineDebug(const CInput *pInput) const
{
    std::string filePath = qPrintable(QDir::toNativeSeparators(pInput->getFileInfo().absoluteFilePath()));
    return ('"' + _targetPath + "\" \"" + filePath + '"'); 
}

void FuzzwinAlgorithm::buildPinCmdLine(const QString &pin_X86,     const QString &pin_X64, 
                                       const QString &pintool_X86, const QString &pintool_X64) 
{
    // si OS 32 bits, pas la peine de spécifier les modules 64bits
    if (_osType < BEGIN_HOST_64BITS) 
    {
        /* $(pin_X86) -t $(pintool_X86) -- $(targetFile) %INPUT% (ajouté a chaque fichier testé) */
        _cmdLinePin =  '"'        + std::string(qPrintable(pin_X86))         \
                     + "\" -t \"" + std::string(qPrintable(pintool_X86))     \
                     + "\" -- \"" + _targetPath + "\" ";
    }
    else
    {
        /* $(pin_X86) -p64 $(pin_X64) -t64 $(pintool_X64) -t $(pintool_X86) 
        -- $(targetFile) %INPUT% (ajouté a chaque fichier testé) */
        _cmdLinePin = '"'          + std::string(qPrintable(pin_X86))      \
                    + "\" -p64 \"" + std::string(qPrintable(pin_X64))      \
                    + "\" -t64 \"" + std::string(qPrintable(pintool_X64))  \
                    + "\" -t \""   + std::string(qPrintable(pintool_X86))  \
                    + "\" -- \""   + _targetPath + "\" ";
    }
}
