#include "algorithmeExpandExecution.h"
#include "check.h"
#include "solver.h"
#include "pintoolFuncs.h"

static UINT32 numberOfChilds = 0;	// numérotation des fichiers dérivés

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
static std::string invertConstraint(const std::string &constraint) 
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

ListOfInputs expandExecution(CInput *pInput, HashTable &h, UINT32 *nbFautes) 
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
        VERBOSE("\tAucune formule recue du pintool !!\n");
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
                CInput *newChild = new CInput(pInput, ++numberOfChilds, j);

                // création du fichier et insertion du contenu modifié
                std::ofstream newFile(newChild->getFilePath(), std::ios::binary);
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
