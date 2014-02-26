===========================
FuzzWin V1.0 - 26/02/2014
Auteur : Sébastien LECOMTE
===========================

------------
Installation
------------
1) Télécharger la dernière version de PIN pour Windows, pour plateforme 
   Visual Studio 2012 (kit vc11) 
   Lien : http://software.intel.com/en-us/articles/pintool-downloads
2) Télécharger Microsoft Z3
   Lien : http://z3.codeplex.com/releases 
3) Extraire les deux archives et définir les variables d'environnement 
   système PIN_ROOT et Z3_ROOT pointant vers la racine des dossiers idoines.
4) Cloner le dépot, ouvrir la solution et compiler en 32bits et en 64bits.

------------
Utilisation:
------------

1) Mode "standalone"
Le pintool est utilisé sans le binaire "FuzzWin". Cela permet d'obtenir la trace
d'exécution d'un programme avec une entrée donnée.
Le mode "standalone" necessite la compilation en mode "DEBUG", en 32 et 64bits
Le mode standalone s'exécute à l'aide du script "PINTOOL_STANDALONE.bat" à la racine
de FuzzWin. Le script contient les instructions et les options possibles

2) Mode "fuzzing"
Après compilation de la solution complète, le répertoire "BUILD" contient les binaires
fuzzwin.exe (mode 32bits) et fuzzwin_x64.exe (mode 64bits), ainsi que les pintools
fuzzwinX86.dll et fuzzwinX64.dll .Pour afficher les options, taper fuzzwin[_x64].exe -h

NB : les scripts "fuzzwin_x86.bat" et "fuzzwin_x64.bat" sont fournis à titre d'exemple