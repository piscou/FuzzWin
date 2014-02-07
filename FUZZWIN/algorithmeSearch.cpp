#include "algorithmeSearch.h"
#include "algorithmeExpandExecution.h"
#include "check.h"

/**********************/
/**  FONCTION SEARCH **/
/**********************/

// cette fonction entretient une liste de fichiers d'entrée et 
// procède aux tests de ces entrées. 
// La fonction retourne le nombre de fichiers qui provoquent une faute
// dans le programme étudié

// TODO : trier la liste à chaque fois que de nouveaux fichiers sont générés, 
// afin d'exécuter en priorité les fichiers ayant une couverture de code maximale
// nécessite l'implémentation d'une fonction de "scoring"

UINT32 algorithmeSearch() 
{
    ListOfInputs workList;		// liste des fichiers à traiter 
    HashValue    fileHash;      // structure pour calculer le hash d'un fichier
    HashTable	 hashTable;		// table de hachage des fichiers déjà traités, pour éviter les doublons
    CInput*		 pFirstInput;	// objet représentant l'entrée initiale
    UINT32		 nbFautes = 0;	// nombre de fautes trouvées au cours de l'analyse
    
    // création de l'objet représentant l'entrée initiale
    std::string firstFilePath(pGlobals->resultDir + "\\input0");
    pFirstInput = new CInput(firstFilePath);
 
    // calcul du hash de la première entrée, et insertion dans la liste des hashes
    hashTable.insert(fileHash(pFirstInput->getFileContent()));

    // initialisation de la liste de travail avec la première entrée
    workList.push_back(pFirstInput);

    /**********************/
    /** BOUCLE PRINCIPALE */
    /**********************/
    while ( !workList.empty() ) 
    {
        std::cout << "[" << workList.size() << "] ELEMENTS DANS LA WORKLIST\n";
        
        // récupération et retrait du fichier ayant le meilleur score (dernier de la liste)
        CInput* pCurrentInput = workList.back();
        workList.pop_back();

        std::cout << "[!] execution de " << pCurrentInput->getFileName();
        std::cout << " (bound = " << pCurrentInput->getBound();
        if (pCurrentInput->getFather()) 
        {
            std::cout << " pere = " << pCurrentInput->getFather()->getFileName();
        }
        std::cout << ")\n";

        // exécution de PIN avec cette entrée (fonction ExpandExecution)
        // et recupération d'une liste de fichiers dérivés
        // la table de hachage permet d'écarter les doublons déjà générés
        auto childInputs = expandExecution(pCurrentInput, hashTable, &nbFautes);

        // insertion des fichiers dans la liste, et diminution du refcount de l'objet venant d'être testé
        workList.insert(workList.cbegin(), childInputs.cbegin(), childInputs.cend());
        pCurrentInput->decRefCount();
    }
    return nbFautes;
}
