#include "call.h"

void CALL::cCALL(INS &ins)
{
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sCALL,
        IARG_INST_PTR, // adresse de l'instrcution appelante
        IARG_UINT32, (UINT32) INS_Size(ins), // adresse de retour mise sur la pile : adresse actuelle + taille
        IARG_END);
}

void CALL::sCALL(ADDRINT callingIp, UINT32 size)
{
    // sauvegarde des adresses appel/retour pour controle lors d'un RET
   //_LOGDEBUG(callingIp << " ---> CALL appelant " <<  " retour "<< (callingIp + size));
   // pTmgr->pushCallRetAdresses(callingIp, callingIp + size);
}