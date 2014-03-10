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
    HashTable	 hashTable;		// table de hachage des fichiers déjà traités, pour éviter les doublons
    CInput*		 pFirstInput;	// objet représentant l'entrée initiale
    UINT32		 nbFautes = 0;	// nombre de fautes trouvées au cours de l'analyse
    
    // création de l'objet représentant l'entrée initiale
    std::string firstFilePath(pGlobals->firstInputPath);
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
        if (pCurrentInput->getFather()) 
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

        // insertion des fichiers dans la liste, et diminution du 
        // refcount de l'objet venant d'être testé
        workList.insert(workList.cbegin(), childInputs.cbegin(), childInputs.cend());
        pCurrentInput->decRefCount();
    }
    return (nbFautes);
}
