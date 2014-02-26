@echo off

rem #############################################
rem #  SCRIPT D'UTILISATION DE FUZZWIN 32BITS  	#
rem #										 	#
rem # Ce script permet de lancer FuzzWin en 	#
rem # mode 32bits								#
rem #										 	#
rem # PREREQUIS 								#
rem # - compilation du pintool en mode "Release"#
rem # - variables d'environnement PIN_ROOT 		#
rem #   et Z3_ROOT définies						#
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

set fuzzwinExe="%~dp0BUILD\fuzzwin.exe"
set resultDir="CheminVersDossierDeResultats"
set INPUT="CheminVersEntreeInitiale"
set EXE="CheminVersExecutable32bits"

%fuzzwinExe% ^
-t %EXE% ^
-i %INPUT% ^
-d %resultDir% ^
--keepfiles ^
--verbose

pause