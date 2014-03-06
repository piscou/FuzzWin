#pragma once
#include "fuzzwin.h"

static const std::string infoHeader
(   
"; **************************************************\n" 
"; *  FUZZWIN : FUZZER AUTOMATIQUE SOUS WINDOWS     *\n" 
"; *  v1.1 (c) Sebastien LECOMTE 02/03/2014         *\n"
"; *  PIN Version 2.13 kit 62732 et Z3 version 4.3  *\n"
"; **************************************************\n" 
);

static const std::string helpMessage
(
"\n"
"FuzzWin - Fuzzer automatique sous plateforme Windows\n"
"\n"
"Usage:  fuzzwin.exe -t <targetExe> - i <firstInput> [options]\n"
"\n"
"Options:\n"
"--help        \t -h : affiche ce message\n"
"--keepfiles   \t -k : conserve les fichiers intermédiaires\n"
"--range       \t -r : intervalles d'octets à marquer (ex: 1-10;15;17-51)\n"
"--dir         \t -d : répertoire de sortie (défaut : './results/')\n"
"--maxconstraints -c : nombre maximal de contraintes à récuperer\n"
"--maxtime     \t -m : temps limite d'exécution de l'exécutable étudie\n"
"--score       \t -s : calcul du score de chaque fichier\n"
"--verbose     \t -v : mode verbeux\n"
);


std::string initialize(int argc, char** argv);