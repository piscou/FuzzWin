@echo off

rem #############################################
rem #     SCRIPT D'UTILISATION DU PINTOOL     	#
rem #										 	#
rem # Ce script permet d'utiliser le pintool	#
rem # sans passer par le binaire FuzzWin		#
rem # A cet effet les arguments sont passés 	#
rem # en ligne de commande						#
rem #										 	#
rem # PREREQUIS 								#
rem # - compilation du pintool en mode "Debug"	#
rem #   en mode 32bits et 64bits				#
rem # - variable d'environnement PIN_ROOT 		#
rem # définie à la racine de PIN				#
rem #										 	#
rem # SORTIE: 									#
rem # dans le répertoire de l'entrée testée 	#
rem # - fichier "xxx_dis.txt" : dessasemblage 	#
rem #   de l'exécution avec le fichier			#
rem # - fichier "xxx_taint.txt" : log de 		#
rem #   marquage des instructions				#
rem # - fichier "xxx_formula.smt2" : formule	#
rem #   au format SMT2 correspondante			#
rem #############################################

rem répertoire de travail
set FuzzwinRoot=%~dp0

rem les DLL suivantes sont créées à la compilation
rem du pintool en 32 et 64bits
set DLLx86="%FuzzwinRoot%BUILD\fuzzwinX86.dll"
set DLLx64="%FuzzwinRoot%BUILD\fuzzwinX64.dll"

rem emplacement des exécutables PIN 32 et 64bits
set pinx86="%PIN_ROOT%ia32\bin\pin.exe"
set pinx64="%PIN_ROOT%intel64\bin\pin.exe"

rem ############################
rem ### ARGUMENTS DU PINTOOL ###
rem ############################

rem nombre maximal de contraintes à récupérér
rem 0 si aucune limite
set maxConstraints=100000

rem temps maximal d'exécution du pintool (en secondes)
rem 0 si aucune limite
set maxTime=0

rem option choisie pour le pintool : 'taint' ou 'checkscore'
set option=taint

rem type d'OS de l'ordniateur hote.
rem peut prendre les valeurs suivantes (cf fichier enumOsType.h) 
rem (NB : ce paramètre est déterminé dynamiquement
rem  par le binaire FuzzWin)
:: 0 = HOST_X86_2000
:: 1 = HOST_X86_XP
:: 2 = HOST_X86_2003
:: 3 = HOST_X86_VISTA_SP0
:: 4 = HOST_X86_VISTA, HOST_X86_2008, HOST_X86_2008_R2
:: 5 = HOST_X86_SEVEN
:: 6 = HOST_X86_WIN8.0, HOST_X86_2012
:: 7 = HOST_X86_WIN8.1, HOST_X86_2012_R2
:: 8 = HOST_X64_BEFORE_WIN8
:: 9 = HOST_X64_WIN8.0
:: 10= HOST_X64_WIN8.1
set ostype=8

rem Définition des plages d'octets à marquer dans le fichier initial. 
rem 'all' si tous les octets sont à marquer
rem la formulation est du type "formulaire d'impression" 
rem ie. intervalles autorisés, groupes séparés par des
rem virgules ou point-virgules. Ex : "1;3; 5-8 , 15 ;16"
rem *** ATTENTION : bien mettre entre guillemets sinon erreur de parsing
set bytesToTaint="all"

rem Temps de latence avant lancement de PIN 
rem permet d'attacher un debugger en s'attachant au PID 
rem du programme lancé, mais non encore exécuté
set pauseTime=10

rem ### ENTREE TESTEE ###
rem
rem *** ATTENTION : les resultats du pintool seront placés
rem *** dans le dossier contenant l'entrée : s'assurer
rem *** d'avoir les droits d'accès à ce dossier, sous peine d'erreur
rem
rem *** ATTENTION(BIS) : pas de chemin avec accents (non géré en mode DEBUG)
set INPUT="CheminSansAccentsVersMonFichier"

rem ### EXECUTABLE TESTE (32 ou 64 bits) ###
set EXE="C:\Windows\system32\notepad.exe"

rem ### LANCEMENT DE PIN ###
rem la version 32bits de PIN est lancée, si l'exécutable est 
rem sur 64bits, il switchera automatiquement
rem sur la version 64 bits de PIN et du PINTOOL

@echo on

%pinx86% ^
-pause_tool %pauseTime% ^
-follow_execv ^
-p64 %pinx64% ^
-t64 %DLLx64% ^
-t %DLLx86% ^
-i %INPUT% ^
-o %option% ^
-k %ostype% ^
-m %maxTime% ^
-c %maxConstraints% ^
-b %bytesToTaint% ^
-- %EXE% %INPUT%

pause