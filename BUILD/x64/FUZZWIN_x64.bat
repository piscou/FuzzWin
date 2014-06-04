@echo off

rem #############################################
rem #  SCRIPT D'UTILISATION DE FUZZWIN 64BITS  	#
rem #										 	#
rem # Ce script permet de lancer FuzzWin en 	#
rem # mode 64bits								#
rem #										 	#
rem # PREREQUIS 								#
rem # - compilation du pintool en mode "Release"#
rem # - variables d'environnement PIN_ROOT 		#
rem #   et Z3_ROOT définies						#
rem #										 	#
rem # SORTIE: 									#
rem # dans le répertoire de résultats		 	#
rem # - fichier "xxx_dis.txt" : dessasemblage 	#
rem #   de l'exécution avec le fichier			#
rem # - fichier "xxx_taint.txt" : log de 		#
rem #   marquage des instructions				#
rem # - fichier "xxx_formula.smt2" : formule	#
rem #   au format SMT2 correspondante			#
rem #############################################

set currentDir=%~dp0

set fuzzwinExe="%currentDir%\x64\fuzzwin_x64.exe"
set resultDir="%currentDir%..\..\TESTS\RESULTATS"
set INPUT="%currentDir%..\..\TESTS\ENTREES INITIALES\pin.txt"
set EXE="%currentDir%..\..\TESTS\EXECUTABLES CIBLES\TEST-EXEx64.exe"

set OPTIONS= --keepfiles

%fuzzwinExe% ^
-t %EXE% ^
-i %INPUT% ^
-d %resultDir% ^
%OPTIONS%q

pause