#include "unconditional_branch.h"

// CALLBACKS
#if TARGET_IA32
void UNCONDITIONAL_BR::cJMP(INS &ins) 
{
    // seuls les cas de type JMP reg ou JMP ea (donc un JMP Near) sont traités
    // Si l'adresse de saut est marquée, alors ajout d'une contrainte
    // qui essaiera de sauter à un autre emplacement
    
    return;

    // cas JMP short : aucun marquage possible, pas d'instrumentation
    if (! INS_IsDirectBranch(ins))
    {
        // cas JMP Near; différencier opérande mémoire / registre
        if (INS_OperandIsMemory(ins, 0)) // opérande mémoire
        {
            REG baseReg  = INS_MemoryBaseReg(ins);  // Registre de base (ou REG_INVALID)
            REG indexReg = INS_MemoryIndexReg(ins); // Registre d'index (ou REG_INVALID)            
            UINT32 addrSize = INS_MemoryReadSize(ins); // taille de l'adresse générée
            INT32 displ = INS_MemoryDisplacement(ins);
            UINT32 scale = INS_MemoryScale(ins);

            void (*callback)() = nullptr;   // pointeur sur la fonction a appeler
            
            if (indexReg == REG_INVALID()) // pas de registre d'index
            {
                // pas de registre de base : aucune propagation possible de marquage 
                if (baseReg == REG_INVALID()) return;
                else // présence base (voire deplacement)
                {
                    callback = (AFUNPTR) ((addrSize == 2) ? sJMP_BD_16 : sJMP_BD_32);
                    INS_InsertCall(ins, IPOINT_BEFORE, callback, 
                        IARG_THREAD_ID,
                        IARG_BRANCH_TARGET_ADDR,    // adresse de saut
                        IARG_UINT32, baseReg,       // registre de base
                        IARG_REG_VALUE, baseReg,    // valeur du registre de base
                        IARG_UINT32, displ,         // valeur du déplacement (pouvant être nul)     
                        IARG_INST_PTR, IARG_END);
                }
            }
            else if (baseReg == REG_INVALID()) // donc index, mais pas de base => ISD
            {
                callback = (AFUNPTR) ((addrSize == 2) ? sJMP_ISD_16 : sJMP_ISD_32);
                INS_InsertCall(ins, IPOINT_BEFORE, callback, 
                    IARG_THREAD_ID,
                    IARG_BRANCH_TARGET_ADDR,    // adresse de saut
                    IARG_UINT32, indexReg,      // registre d'index
                    IARG_REG_VALUE, indexReg,   // valeur du registre d'index
                    IARG_UINT32, scale,         // valeur du scale
                    IARG_UINT32, displ,         // valeur du déplacement     
                    IARG_INST_PTR, IARG_END);
            }
            else // base et index présents => BISD
                {
                    callback = (AFUNPTR) ((addrSize == 2) ? sJMP_BISD_16 : sJMP_BISD_32);
                    INS_InsertCall(ins, IPOINT_BEFORE, callback, 
                        IARG_THREAD_ID,
                        IARG_BRANCH_TARGET_ADDR,    // adresse de saut
                        IARG_UINT32, baseReg,       // registre de base
                        IARG_REG_VALUE, baseReg,    // valeur du registre de base
                        IARG_UINT32, indexReg,      // registre d'index
                        IARG_REG_VALUE, indexReg,   // valeur du registre d'index
                        IARG_UINT32, scale,         // valeur du scale
                        IARG_UINT32, displ,         // valeur du déplacement
                        IARG_INST_PTR, IARG_END);
                }             
        }
        else // forcemément, destination registre
        {
            REG regJmp = INS_OperandReg(ins, 0);
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sJMP_R, 
                IARG_THREAD_ID,
                IARG_UINT32, regJmp,    // registre "trampoline"
                IARG_REG_VALUE, regJmp, //  valeur du registre = adresse de saut
                IARG_INST_PTR, IARG_END);
        }
    }
} // cJMP(32bits)
#else
void UNCONDITIONAL_BR::cJMP(INS &ins) 
{
    // seuls les cas de type JMP reg ou JMP ea (donc un JMP Near) sont traités
    // Si l'adresse de saut est marquée, alors ajout d'une contrainte
    // qui essaiera de changer cette addresse afin de sauter à un autre emplacement
    
    // cas JMP short : aucun marquage possible, pas d'instrumentation
    if (! INS_IsDirectBranch(ins))
    {
        // cas JMP Near; différencier opérande mémoire / registre
        if (INS_OperandIsMemory(ins, 0)) // opérande mémoire
        {
            REG baseReg = INS_MemoryBaseReg(ins);  // Registre de base (ou REG_INVALID)
           
            // cas "rip-relative" (x64 uniquement) non marquable => ne pas instrumenter
            if (baseReg == REG_RIP)  return;

            REG indexReg    = INS_MemoryIndexReg(ins); // Registre d'index (ou REG_INVALID)            
            UINT32 addrSize = INS_MemoryReadSize(ins); // taille de l'adresse générée
            INT32 displ     = static_cast<INT32>(INS_MemoryDisplacement(ins));
            UINT32 scale    = INS_MemoryScale(ins);

            if (indexReg == REG_INVALID()) // pas de registre d'index
            {
                // pas de registre de base : aucune propagation possible de marquage 
                if (baseReg == REG_INVALID()) return;
                else // présence base (voire deplacement)
                {
                    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sJMP_BD_64, 
                        IARG_THREAD_ID,
                        IARG_BRANCH_TARGET_ADDR,    // adresse de saut
                        IARG_UINT32, baseReg,       // registre de base
                        IARG_REG_VALUE, baseReg,    // valeur du registre de base
                        IARG_UINT32, displ,         // valeur du déplacement (pouvant être nul)     
                        IARG_INST_PTR, IARG_END);
                }
            }
            else if (baseReg == REG_INVALID()) // donc index, mais pas de base => ISD
            {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sJMP_ISD_64, 
                    IARG_THREAD_ID,
                    IARG_BRANCH_TARGET_ADDR,    // adresse de saut
                    IARG_UINT32, indexReg,      // registre d'index
                    IARG_REG_VALUE, indexReg,   // valeur du registre d'index
                    IARG_UINT32, scale,         // valeur du scale
                    IARG_UINT32, displ,         // valeur du déplacement     
                    IARG_INST_PTR, IARG_END);
            }
            else // base et index présents => BISD
            {
                INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sJMP_BISD_64, 
                    IARG_THREAD_ID,
                    IARG_BRANCH_TARGET_ADDR,    // adresse de saut
                    IARG_UINT32, baseReg,       // registre de base
                    IARG_REG_VALUE, baseReg,    // valeur du registre de base
                    IARG_UINT32, indexReg,      // registre d'index
                    IARG_REG_VALUE, indexReg,   // valeur du registre d'index
                    IARG_UINT32, scale,         // valeur du scale
                    IARG_UINT32, displ,         // valeur du déplacement
                    IARG_INST_PTR, IARG_END);
            }             
        }
        else // forcemément, destination registre
        {
            REG regJmp = INS_OperandReg(ins, 0);
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) sJMP_R, 
                IARG_THREAD_ID,
                IARG_UINT32, regJmp,    // registre "trampoline"
                IARG_REG_VALUE, regJmp, //  valeur du registre = adresse de saut
                IARG_INST_PTR, IARG_END);
        }
    }
} // cJMP(64bits)
#endif

#if TARGET_IA32
// x86 : Effective Address vaut 16 ou 32 bits

void UNCONDITIONAL_BR::sJMP_BD_16(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, INT32 displ, ADDRINT insAddress)
{  }

void UNCONDITIONAL_BR::sJMP_ISD_16(THREADID tid, ADDRINT ea, REG indexReg, ADDRINT indexRegValue, 
                 UINT32 scale, INT32 displ, ADDRINT insAddress)
{   }

void UNCONDITIONAL_BR::sJMP_BISD_16(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, 
                  REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ, ADDRINT insAddress)
{ }


void UNCONDITIONAL_BR::sJMP_BD_32(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, INT32 displ, ADDRINT insAddress)
{  }

void UNCONDITIONAL_BR::sJMP_ISD_32(THREADID tid, ADDRINT ea, REG indexReg, ADDRINT indexRegValue, 
                 UINT32 scale, INT32 displ, ADDRINT insAddress)
{ }

void UNCONDITIONAL_BR::sJMP_BISD_32(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, 
                  REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ, ADDRINT insAddress)
{  }

void UNCONDITIONAL_BR::sJMP_R(THREADID tid, REG reg, ADDRINT regValue, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if (pTmgrTls->isRegisterTainted<32>(reg))
    {
        _LOGDEBUG("JMP_REG Registre marqué !!!");
    }
    else
    {
        _LOGDEBUG("JMP_REG Registre NON MARQUE");
    }
}

#else
// x64 : Effective Address vaut 64 bits uniquement

void UNCONDITIONAL_BR::sJMP_BD_64(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, INT32 displ, ADDRINT insAddress)
{ }

void UNCONDITIONAL_BR::sJMP_ISD_64(THREADID tid, ADDRINT ea, REG indexReg, ADDRINT indexRegValue, 
                 UINT32 scale, INT32 displ, ADDRINT insAddress)
{  }

void UNCONDITIONAL_BR::sJMP_BISD_64(THREADID tid, ADDRINT ea, REG baseReg, ADDRINT baseRegValue, 
                  REG indexReg, ADDRINT indexRegValue, UINT32 scale, INT32 displ, ADDRINT insAddress)
{ }

void UNCONDITIONAL_BR::sJMP_R(THREADID tid, REG reg, ADDRINT regValue, ADDRINT insAddress) 
{
    TaintManager_Thread *pTmgrTls = getTmgrInTls(tid);
    
    if (pTmgrTls->isRegisterTainted<64>(reg)) 
    {
        _LOGDEBUG("JMP_REG Registre marqué !!!");
    }
    else 
    {
        _LOGDEBUG("JMP_REG Registre NON MARQUE");
    }
}
#endif

