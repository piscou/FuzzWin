FuzzWin
=======

Auteur : Sébastien LECOMTE   
Version 1.5 du 04/06/2014
**************************

Installation
------------

1. Télécharger PIN pour Windows, kit "vc11" version 2.13-62732  
   (<http://software.intel.com/sites/landingpage/pintool/downloads/pin-2.13-62732-msvc11-windows.zip>) 
2. Télécharger Microsoft Z3 (<http://z3.codeplex.com/releases>) 
3. Extraire les deux archives et définir les variables d'environnement système PIN\_ROOT et Z3\_ROOT pointant vers la racine des dossiers idoines.
4. compiler les sources (solution Visual Studio 2012) en fonction de l'architecture cible 32 ou 64bits.

NB : 
- la compilation du mode GUI necessite l'installation de Qt version 5.2. 
  Les DLL sont fournies dans les dossiers x86 et x64 du dépot
- le mode x64 necessite la compilation du pintool en mode 32 et 64 bits

Utilisation
-----------

FuzzWin peut s'exécuter en mode graphique ou ligne de commande. 
Pour plus d'informations sur les options, taper fuzzwin.exe -h

Licence
-------

FuzzWin est un projet libre sous licence GPLV2 (cf fichier LICENSE à la racine du dépot).
FuzzWin utilise PIN, dont la licence d'utilisation figure dans le package téléchargé.
Un rappel de la licence de PIN figure dans le fichier main.cpp du pintool

Contact
-------
cyberaware@laposte.net