#include "call.h"

void CALL::cCALL(INS &ins, bool isFarCall)
{
    void (*callback)() = nullptr;

    /* CALL est étudié lorsqu'il est possible d'influer sur l'adresse du saut
    donc les cas "CALL relative" (adresse immédiate ou relative à EIP) sont non traités */

    if (INS_IsDirectCall(ins))
    {
        _LOGDEBUG("CALL DIRECT NON SUIVI " + decstr(INS_MemoryWriteSize(ins)));
        // démarquage de la pile : impossible de faire appel à uMEM
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) UTILS::uMEM, 
            IARG_FAST_ANALYSIS_CALL,  
            IARG_MEMORYWRITE_EA,
            IARG_MEMORYWRITE_SIZE,
            IARG_END);

        return;
    }

    /* traiter deux cas:
      1) CALL [EFFECTIVE ADDRESS] : il faut tester à la fois si le calcul de l'adresse
         effective est marqué (appel à cGetKindOfEA) et si l'adresse du saut, figurant
         à l'adresse effective, est marquée
         qui va vérifier si le calcul de l'EA est marqué ou non
      2) CALL REG : il faut tester le marquage du registre concerné. si c'est le cas
         il faudra essayer de changer sa valeur pour sauter autre part */

    // la différence entre call NEAR et FAR, au niveua marquage, est la taille
    // du démarquage de la pile : le call FAR stocke CS (16 bit) en plus sur la pile

    // cas n°1 : CALL [EFFECTIVE ADDRESS] 
    if (INS_OperandIsMemory(ins, 0)) 
    {
        if (isFarCall)
        {
            _LOGDEBUG("CALL_M (FAR)");
        }
        else  _LOGDEBUG("CALL_M (NEAR)");

        // test du marquage de l'adresse effective par insertion de callbacks spécifiques
        UTILS::cGetKindOfEA(ins);

        // taille de lecture de la mémoire (16, 32 ou 64 bits)
        switch (INS_MemoryReadSize(ins))
        {
        // case 1:	impossible
        case 2:	callback = (AFUNPTR) sCALL_M<16>; break;
        case 4:	callback = (AFUNPTR) sCALL_M<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sCALL_M<64>; break;
        #endif
        }

        INS_InsertCall(ins, IPOINT_BEFORE, callback, 
            IARG_THREAD_ID,
            IARG_BOOL, isFarCall,   // call NEAR ou FAR
            IARG_MEMORYREAD_EA,             // adresse ou se trouve l'adresse de saut
            IARG_BRANCH_TARGET_ADDR,        // adresse de saut     
            IARG_REG_VALUE, REG_STACK_PTR,  // adresse de la pile (pour démarquage)
            IARG_INST_PTR, IARG_END);
    } 
    // cas n°2 : CALL 'REG'
    else
    {
        if (isFarCall)
        {
            _LOGDEBUG("CALL_R (FAR)");
        }
        else  _LOGDEBUG("CALL_R (NEAR)");

        REG reg = INS_OperandReg(ins, 0);

        switch (getRegSize(reg))
        {
        // case 1:	impossible
        case 2:	callback = (AFUNPTR) sCALL_R<16>; break;
        case 4:	callback = (AFUNPTR) sCALL_R<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sCALL_R<64>; break;
        #endif
        }
      
        INS_InsertCall(ins, IPOINT_BEFORE, callback, 
            IARG_THREAD_ID,   
            IARG_BOOL,      isFarCall,   // call NEAR ou FAR
            IARG_UINT32,    reg,     // registre définissant l'adresse de saut
            IARG_BRANCH_TARGET_ADDR, // adresse de saut (=valeur du registre masqué à 16/32/64bits)  
            IARG_REG_VALUE, REG_STACK_PTR,  // adresse de la pile (pour démarquage)
            IARG_INST_PTR, IARG_END);
    } 
}

