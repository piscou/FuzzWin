#include "unconditional_branch.h"

// CALLBACKS
void UNCONDITIONAL_BR::cJMP(INS &ins) 
{
    void (*callback)() = nullptr;
    
    /* JMP est étudié lorsqu'il est possible d'influer sur l'adresse du saut
    donc les cas "JMP relative" (adresse immédiate ou relative à EIP) sont non traités */

    if (INS_IsDirectBranch(ins)) return;

    /* dans le cas contraire il reste à traiter deux cas:
      1) JMP [EFFECTIVE ADRESS] : il faut tester à la fois si le calcul de l'adresse
         effective est marqué (appel à cGetKindOfEA) et si l'adresse du saut, figurant
         à l'adresse effective, est marquée
         qui va vérifier si le calcul de l'EA est marqué ou non
      2) JMP REG : il faut tester le marquage du registre concerné. si c'est le cas
         il faudra essayer de changer sa valeur pour sauter autre part */

    // cas n°1 : JMP [EFFECTIVE ADDRESS] 
    if (INS_OperandIsMemory(ins, 0)) 
    {
        // test du marquage de l'adresse effective par insertion de callbacks spécifiques
        UTILS::cGetKindOfEA(ins);

        // taille de lecture de la mémoire (16, 32 ou 64 bits)
        switch (INS_MemoryReadSize(ins))
        {
        // case 1:	impossible
        case 2:	callback = (AFUNPTR) sJMP_M<16>; break;
        case 4:	callback = (AFUNPTR) sJMP_M<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sJMP_M<64>; break;
        #endif
        }

        // insertion du callback pour le test du marquage de l'adresse pointée par l'EA
        INS_InsertCall(ins, IPOINT_BEFORE, callback, 
            IARG_THREAD_ID,
            IARG_MEMORYREAD_EA,    // adresse ou se trouve l'adresse de saut
            IARG_BRANCH_TARGET_ADDR,    // adresse de saut     
            IARG_INST_PTR, IARG_END);
    } 
    // cas n°2 : JMP 'REG'
    else
    {
        REG reg = INS_OperandReg(ins, 0);

        switch (getRegSize(reg))
        {
        // case 1:	impossible
        case 2:	callback = (AFUNPTR) sJMP_R<16>; break;
        case 4:	callback = (AFUNPTR) sJMP_R<32>; break;
        #if TARGET_IA32E
        case 8: callback = (AFUNPTR) sJMP_R<64>; break;
        #endif
        }
      
        INS_InsertCall(ins, IPOINT_BEFORE, callback, 
            IARG_THREAD_ID,   
            IARG_UINT32,    reg,     // registre définissant l'adresse de saut
            IARG_BRANCH_TARGET_ADDR, // adresse de saut   
            IARG_INST_PTR, IARG_END);
    }
} // cJMP
