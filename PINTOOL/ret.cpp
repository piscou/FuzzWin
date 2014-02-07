#include "ret.h"
#include "TaintManager.h"

void RET::cRET(INS &ins)
{
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sRET,
        IARG_INST_PTR, // adresse de l'instruction 
        IARG_BRANCH_TARGET_ADDR, // adresse de retour 
        IARG_END);
}

void RET::sRET(ADDRINT insAddress, ADDRINT returnIp)
{
    // récupération de l'adresse de retour présente sur la pile
    // TODO : voir si la pile n'est pas marquée à cet emplacement !!!

    // recupération des adresses appel/retour sauvegardées
    //auto savedAddress = pTmgr->getCallRetAdresses();
   // ADDRINT savedCallee = savedAddress.first;
   // ADDRINT savedReturnIp = savedAddress.second;
   // if (savedCallee) // si nul, alors on était sur un "RET" qui n'avait pas de call (cas initial)
    //{    
       // _LOGDEBUG(" ---> RET retour effectif " << returnIp << " prévu "<< savedReturnIp << " appel fait en " << savedCallee);
  //  }
}