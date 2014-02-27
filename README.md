FuzzWin V1.0
============

Auteur : Sébastien LECOMTE   
Version 1.0 du 26/02/2014
**************************

Installation
------------

1. Télécharger la dernière version de PIN pour Windows, kit "vc11"    
   (<http://software.intel.com/en-us/articles/pintool-downloads>) 
2. Télécharger Microsoft Z3 (<http://z3.codeplex.com/releases>) 
3. Extraire les deux archives et définir les variables d'environnement système PIN\_ROOT et Z3\_ROOT pointant vers la racine des dossiers idoines.
4. Cloner le dépot, ouvrir la solution et compiler en 32bits et en 64bits.

Utilisation
-----------

1. Mode *standalone*  
Le pintool est utilisé sans le binaire "FuzzWin". Cela permet d'obtenir la trace d'exécution d'un programme avec une entrée donnée.  
Le mode "standalone" nécessite la compilation en mode *DEBUG* en 32bits et 64bits. Le mode standalone s'exécute à l'aide du script "PINTOOL\_STANDALONE.bat" à la racine de FuzzWin. Le script contient les instructions et les options possibles.  
2. Mode *fuzzing*  
Après compilation de la solution complète, le répertoire "BUILD" contient les binaires *fuzzwin.exe* et *fuzzwin_x64.exe*, ainsi que les pintools *fuzzwinX86.dll* et *fuzzwinX64.dll*.
Pour afficher les options, taper *fuzzwin[\_x64].exe -h*

NB : les scripts *fuzzwin\_x86.bat* et *fuzzwin\_x64.bat* sont fournis à titre d'exemple