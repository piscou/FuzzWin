#include "algorithmeExpandExecution.h"
#include "check.h"
#include "solver.h"

#include <sstream> // stringstream

static UINT32 numberOfChilds = 0;	// numérotation des fichiers dérivés

class CPinCommandsParameters
{
public:
    const char* _filePath;
    DWORD _filePathLength;
    CPinCommandsParameters(const char* f, DWORD l) : _filePath(f), _filePathLength(l) {}
    ~CPinCommandsParameters() {}
};

/*********************************/
/**  ALGORITHME EXPANDEXECUTION **/
/*********************************/

// cette fonction génère de nouveaux fichiers d'entrée à partir d'une entrée fournie
// 1) exécution du premier PINTOOL ("FuzzWin") retournant une formule SMT2 brute
// 2) récupération du nombre de contraintes dans ce fichier
// 3) pour j dans [bound + 1, nbContraintes] :
//		inverser la contrainte numéro J et envoyer la formule au solveur
//		si une solution existe :  
//			génération d'un nouveau fichier avec les octets modifiés
//			calcul du hash, si déjà présent ne pas retenir la solution
//			atribution du "bound" = j à ce nouveau fichier
//			ajout du fichier à la liste des fichiers générés
//	 (fin de la boucle j)
// retour de la liste des fichiers ainsi générés

static size_t sendNonInvertedConstraints(const std::string &formula, UINT32 bound)
{
    size_t posBeginOfLine = 0; // position du début de ligne de la contrainte 'bound'
    size_t posEndOfLine   = 0; // position du fin de ligne de la contrainte 'bound'

    if (bound) 
    {
        // recherche de la contrainte "bound" dans la formule
        posBeginOfLine	= formula.find("(assert (= C_" + std::to_string((_Longlong) bound));
        // recherche de la fin de la ligne
        posEndOfLine	= formula.find_first_of('\n', posBeginOfLine);
        // extraction des contraintes non inversées et envoi au solveur
        sendToSolver(formula.substr(0, posEndOfLine + 1));
    }
    return (posEndOfLine); // position de la fin de la dernière contrainte dans la formule
}

static std::string invertConstraint(std::string constraint) // copie locale de la contrainte originale
{
    size_t pos = constraint.find("true");
    
    if (pos != std::string::npos)    constraint.replace(pos, 4, "false");   // 'true'  -> 'false' 
    else  constraint.replace(constraint.find("false"), 5, "true");          // 'false' -> 'true'

    return (constraint);
}

static int sendArgumentsToPintool(const std::string &command)
{
    // 1) chemin vers l'entrée étudiée
    // 2) nombre maximal de contraintes (TODO)
    // 3) temps limite d'execution en secomdes (TODO)
    // 4) offset des entrees à etudier (TODO)
    
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
        std::cout << "erreur envoi arguments au Pintool" << std::endl;
        return 1;   // erreur
    }
    else return 0;  // OK
}


static std::string callFuzzwin(CInput* pInput) 
{
    // ligne de commande pour appel de PIN avec l'entree etudiee
    std::string cmdLine(pInput->getCmdLineFuzzwin()); 
    std::string smtFormula;
  
    STARTUPINFO si;
    PROCESS_INFORMATION pi;
    
    ZeroMemory(&si, sizeof(si));
    ZeroMemory(&pi, sizeof(pi));
    si.cb = sizeof(si);
    
    if (CreateProcess (nullptr, (LPSTR) cmdLine.c_str(), nullptr, nullptr, TRUE, NULL, nullptr, nullptr, &si, &pi)) 
    {          
        /***********************/
        /** CONNEXION AU PIPE **/
        /***********************/
        BOOL fSuccess;
        fSuccess = ConnectNamedPipe(pGlobals->hPintoolPipe, NULL);
        if (!fSuccess && GetLastError() != ERROR_PIPE_CONNECTED) 
        {	
            std::cout << "erreur de connexion au pipe FuzzWin" << GetLastError() << std::endl;
            return (smtFormula); // formule vide
        }
        
        /************************************/
        /** ENVOI DES ARGUMENTS AU PINTOOL **/
        /************************************/

        int resultOfSend;
        // 1) chemin vers l'entrée étudiée
        resultOfSend = sendArgumentsToPintool(pInput->getFilePath());
        // 2) nombre maximal de contraintes (TODO)
        // 3) temps limite d'execution en secomdes (TODO)
        std::string maxTime(std::to_string(pGlobals->maxExecutionTime));
        resultOfSend = sendArgumentsToPintool(maxTime);
        // 4) offset des entrees à etudier (TODO)
        resultOfSend = sendArgumentsToPintool(pGlobals->bytesToTaint);

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
 
            if ( ! fSuccess && GetLastError() != ERROR_MORE_DATA )  break; 
            // ajout des données lues au resultat
            smtFormula.append(&buffer[0], cbBytesRead);

         } while ( ! fSuccess);  // repetition si ERROR_MORE_DATA 

        // deconnexion du pipe
        DisconnectNamedPipe(pGlobals->hPintoolPipe);

        // attente de la fermeture de l'application
        WaitForSingleObject(pi.hProcess, INFINITE);
        
        // recupération du code de retour du pinttol (pour éventuel debug)
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
    else // si erreur de CreateProcess
    {
        VERBOSE(std::cout << "erreur process FuzzWin" << GetLastError() << std::endl;)
    }
    
    return (smtFormula); // retour de la formule SMT2
}

ListOfInputs expandExecution(CInput *pInput, HashTable &h, UINT32 *nbFautes) 
{  
    ListOfInputs result;	                // liste de nouveaux objets de type CInput générées
    UINT32	bound = pInput->getBound();     // bound du fichier actuellement étudié
    size_t pos = 0, posLastConstraint = 0;  // indexs de position dans une chaine de caractères
    std::string inputContent;               // contenu du fichier étudié
    std::string	constraintJ;	        // partie de formule associée à la contrainte J
    std::string constraintJ_inverted;   // la même contrainte, inversée
    std::string formula;            // formule fournie par le pintool lors de l'exécution du fichier 'pInput'
    static HashValue   fileHash;    // structure pour calculer le hash d'un fichier

    /********************************************************/
    /** Execution du pintool et récupération de la formule **/
    /********************************************************/
    formula = callFuzzwin(pInput);
    if (formula.size() == 0) return result; // aucune formule ou erreur

    // récupération du nombre de contraintes dans la formule
    pos = formula.find_last_of('@');
    if (pos == std::string::npos) return result;
    UINT32 nbContraintes = std::stoi(formula.substr(pos + 1));

    // si le "bound" est supérieur aux nombre de contraintes => aucune nouvelle entrée, retour
    if (bound >= nbContraintes) 	
    {
        std::cout << "\tPas de nouvelles contraintes inversibles" << std::endl;
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
        VERBOSE(std::cout << "\tinversion contrainte " << j);
            
        // recherche de la prochaine contrainte dans la formule, à partir de la position de la précédente contrainte 
        pos = formula.find("(assert (=", posLastConstraint);          
        // envoi au solveur de toutes les déclarations avant la contrainte
        sendToSolver(formula.substr(posLastConstraint, (pos - posLastConstraint)));
        // envoi au solveur de la commande "push 1"
        // reserve une place sur la pile pour la prochaine déclaration (la contrainte inversée)
        sendToSolver("(push 1)\n");

        // recherche de la fin de la ligne de la contrainte actuelle (et future précédente contrainte)
        posLastConstraint = formula.find_first_of('\n', pos);     
        // extraction de la contrainte, et inversion
        constraintJ = formula.substr(pos, (posLastConstraint - pos));
        constraintJ_inverted = invertConstraint(constraintJ);    

        // envoi de la contrainte J inversée au solveur, et recherche de la solution
        sendToSolver(constraintJ_inverted + '\n');

        if (checkSatFromSolver())	// SOLUTION TROUVEE : DEMANDER LES RESULTATS
        {							
            std::string newInputContent(inputContent); // copie du contenu du fichier initial
            std::string solutions;
            size_t      newFileHash = 0;
             
            // récupération des solutions du solveur
            solutions = getModelFromSolver();
                
            // modification des octets concernés dans le contenu du nouveau fichier
            std::sregex_token_iterator it (solutions.begin(), solutions.end(), pGlobals->regexModel, pGlobals->tokens);
            std::sregex_token_iterator end;
            while (it != end) 
            {
                int offset = std::stoi(it->str(), nullptr, 10); ++it; // 1ere valeur = offset
                int value =  std::stoi(it->str(), nullptr, 16); ++it; // 2eme valeur = valeur
                newInputContent[offset] = static_cast<char>(value);
            }

            // calcul du hash du nouveau contenu et insertion dans la table de hachage. 
            // Si duplicat (retour 'false'), ne pas créer le fichier
            auto insertResult = h.insert(fileHash(newInputContent));
            if (insertResult.second != false)
            {
                // fabrication du nouvel objet "fils" à partir du père
                CInput *newChild = new CInput(pInput, ++numberOfChilds, j);

                // création du fichier et insertion du contenu modifié
                std::ofstream newFile(newChild->getFilePath(), std::ios::binary);
                newFile.write(newInputContent.c_str(), newInputContent.size());
                newFile.close();

                VERBOSE(std::cout << "-> nouveau fichier " << newChild->getFileName() << std::endl);

                // test du fichier de suite; si retour nul le fichier est valide, donc l'insérer dans la liste
                DWORD checkError = debugTarget(newChild);
                if (!checkError) result.push_back(newChild);
                else ++*nbFautes;

            }	// fin de la boucle de test sur le hash du contenu
            else 	VERBOSE(std::cout << "-> deja genere\n");
        } // end "hasSolution"
        else VERBOSE(std::cout << " : aucune solution\n");   
       
        // enlever la contrainte inversée de la pile du solveur, et remettre l'originale
        sendToSolver("(pop 1)\n" + constraintJ);
    } // end for
       
    // effacement de toutes les formules pour laisser une pile vierge pour le prochain fichier
    sendToSolver("(reset)\n");

    return (result);
}
