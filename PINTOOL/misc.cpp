#include "MISC.h"
#include "utils.h"

/////////
// LEA //
/////////
// CALLBACKS
void MISC::cLEA(INS &ins) 
{
    REG regDest = INS_RegW(ins, 0);            // registre de destination
    UINT32 regDestSize = getRegSize(regDest);   // taille du registre dest ("OperandSize") 
    if (!regDestSize) return;                   // registre destination non géré

    REG baseReg  = INS_MemoryBaseReg(ins);  // Registre de base (ou REG_INVALID)
    REG indexReg = INS_MemoryIndexReg(ins); // Registre d'index (ou REG_INVALID)
    UINT32 addrSize = INS_EffectiveAddressWidth(ins); // taille de l'adresse générée
    void (*callback)() = nullptr;                     // pointeur sur la fonction a appeler

    // afin d'optimiser les arguments passés aux fonctions d'analyse, 3 cas sont distingués
    // Base mais pas d'Index (seul => CAS B ou MOV ou MOVZX, ou avec déplacement => CAS BD) 
    // Index mais pas de Base : LEA_ISD avec déplacement nul ou non et scale nul ou non
    // Index et BAse : LEA_BISD avec déplacement nul ou non et scale nul ou non

    if (indexReg == REG_INVALID()) // Si aucun registre d'index
    {    
        if (baseReg == REG_INVALID()) // ni registre de base : CAS DISPLACEMENT : démarquage
        {          
            switch (regDestSize)  
            {
            // case 1: impossible pour LEA
            case 2: callback = (AFUNPTR) UTILS::uREG<16>;  break;
            case 4: callback = (AFUNPTR) UTILS::uREG<32>;  break;
            #if TARGET_IA32E
            case 8: callback = (AFUNPTR) UTILS::uREG<64>;  break;
            #endif
            }

            INS_InsertCall (ins, IPOINT_BEFORE, callback,
                IARG_FAST_ANALYSIS_CALL,
                IARG_THREAD_ID,
                IARG_UINT32, regDest, // registre de destination à démarquer
                IARG_END);
        }
        else // donc forcément un registre de base, mais pas d'index : cas LEA_BD
        {
            // récupération du déplacement (toujours sur 4 octets, y compris en 64bits)
            INT32 displ = static_cast<INT32>(INS_MemoryDisplacement(ins));     
   
            // en 64 bit, il existe un mode d'adressage spécial : RIP-relative
            // le registre de base peut donc etre RIP (qui n'est pas géré en marquage)
            #if TARGET_IA32E
            if (baseReg == REG_RIP) 
            {
                switch (regDestSize) 
                {
                // case 1: impossible pour LEA
                case 2: callback = (AFUNPTR) UTILS::uREG<16>;  break;
                case 4: callback = (AFUNPTR) UTILS::uREG<32>;  break;   
                case 8: callback = (AFUNPTR) UTILS::uREG<64>;  break;
                }
                    
                INS_InsertCall (ins, IPOINT_BEFORE, callback,
                    IARG_THREAD_ID,
                    IARG_FAST_ANALYSIS_CALL,
                    IARG_UINT32, regDest, // registre de destination à démarquer
                    IARG_END);
                    
                return; // fin de l'instrumentation
            }
            #endif

            switch (regDestSize) 
            {
            // case 1: impossible pour LEA
            case 2: // operandSize de 16 bits
           
                #if TARGET_IA32  // en 32 bits : adressSize vaut soit 16, soit 32bits
                callback = (AFUNPTR) ((addrSize == 16) ? sLEA_BD<16, 16> : sLEA_BD<32, 16>);
                #else // en 64 bits : adressSize vaut soit 32, soit 64bits
                callback = (AFUNPTR) ((addrSize == 32) ? sLEA_BD<32, 16> : sLEA_BD<64, 16>);
                #endif
                    
                break;  
            case 4:   // operandSize de 32bits  
                    
                #if TARGET_IA32  // en 32 bits : adressSize vaut soit 16, soit 32bits
                callback = (AFUNPTR) ((addrSize == 16) ? sLEA_BD<16, 32> : sLEA_BD<32, 32>);                
                #else // en 64 bits : adressSize vaut soit 32, soit 64bits
                callback = (AFUNPTR) ((addrSize == 32) ? sLEA_BD<32, 32> : sLEA_BD<64, 32>);
                #endif

                break;  
            #if TARGET_IA32E
            case 8:   // operandSize de 64bits : adressSize vaut soit 32, soit 64bits
                callback = (AFUNPTR) ((addrSize == 32) ? sLEA_BD<32, 64> : sLEA_BD<64, 64>);
                break;  
            #endif
            }
                
            INS_InsertCall(ins, IPOINT_BEFORE, callback,
                IARG_THREAD_ID,
                IARG_UINT32,    regDest, // registre de destination 
                IARG_UINT32,    baseReg, // registre de base utilisé
                IARG_REG_VALUE, baseReg, // valeur lors du callback
                IARG_UINT32,    displ,  // déplacement (valeur signée castée en non signée)
                CALLBACK_DEBUG IARG_END);
            
        }
    }
    // présence d'un index, mais pas de registre de base
    else if (baseReg == REG_INVALID() ) // CAS LEA_ISD (displ nul ou non, scale = 1 ou non)
    {                                
        switch (regDestSize) 
        {
        // case 1: impossible pour LEA
        case 2: // operandSize de 16 bits
      
            #if TARGET_IA32  // en 32 bits : adressSize vaut soit 16, soit 32bits
            callback = (AFUNPTR) ((addrSize == 16) ? sLEA_ISD<16, 16> : sLEA_ISD<32, 16>);
            #else // en 64 bits : adressSize vaut soit 32, soit 64bits
            callback = (AFUNPTR) ((addrSize == 32) ? sLEA_ISD<32, 16> : sLEA_ISD<64, 16>);
            #endif
                    
            break;  
        case 4:   // operandSize de 32bits  
                   
            #if TARGET_IA32  // en 32 bits : adressSize vaut soit 16, soit 32bits
            callback = (AFUNPTR) ((addrSize == 16) ? sLEA_ISD<16, 32> : sLEA_ISD<32, 32>);                
            #else // en 64 bits : adressSize vaut soit 32, soit 64bits
            callback = (AFUNPTR) ((addrSize == 32) ? sLEA_ISD<32, 32> : sLEA_ISD<64, 32>);
            #endif

            break;  
        #if TARGET_IA32E
        case 8:   // operandSize de 64bits : adressSize vaut soit 32, soit 64bits
            callback = (AFUNPTR) ((addrSize == 32) ? sLEA_ISD<32, 64> : sLEA_ISD<64, 64>);
            break;  
        #endif
        }

        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,    regDest, // registre de destination 
            IARG_UINT32,    indexReg,               // registre d'index utilisé
            IARG_REG_VALUE, indexReg,               // valeur lors du callback
            IARG_UINT32,    INS_MemoryScale(ins),   // valeur du scale (0 si aucun)
            IARG_UINT32,    INS_MemoryDisplacement(ins),  // déplacement (0 si aucun)
            CALLBACK_DEBUG IARG_END);
    }
    // registre de base ET d'index présents 
    else  // cas BASE + INDEX*SCALE + DISP  : LEA BISD (displ nul ou non, scale = 1 ou non)
    {     
        switch (regDestSize) 
        {
        // case 1: impossible pour LEA
        case 2: // operandSize de 16 bits
                    
            #if TARGET_IA32  // en 32 bits : adressSize vaut soit 16, soit 32bits
            callback = (AFUNPTR) ((addrSize == 16) ? sLEA_BISD<16, 16> : sLEA_BISD<32, 16>);
            #else // en 64 bits : adressSize vaut soit 32, soit 64bits
            callback = (AFUNPTR) ((addrSize == 32) ? sLEA_BISD<32, 16> : sLEA_BISD<64, 16>);
            #endif       
            break;  
        case 4:   // operandSize de 32bits  
                    
            #if TARGET_IA32  // en 32 bits : adressSize vaut soit 16, soit 32bits
            callback = (AFUNPTR) ((addrSize == 16) ? sLEA_BISD<16, 32> : sLEA_BISD<32, 32>);                
            #else // en 64 bits : adressSize vaut soit 32, soit 64bits
            callback = (AFUNPTR) ((addrSize == 32) ? sLEA_BISD<32, 32> : sLEA_BISD<64, 32>);
            #endif
            break;  
        #if TARGET_IA32E
        case 8:   // operandSize de 64bits : adressSize vaut soit 32, soit 64bits
            callback = (AFUNPTR) ((addrSize == 32) ? sLEA_BISD<32, 64> : sLEA_BISD<64, 64>);
            break;  
        #endif
        }
       
        INS_InsertCall (ins, IPOINT_BEFORE, callback,
            IARG_THREAD_ID,
            IARG_UINT32,    INS_OperandReg(ins, 0), // registre de destination 
            IARG_UINT32,    baseReg,                // registre de base utilisé
            IARG_REG_VALUE, baseReg,                // valeur lors du callback
            IARG_UINT32,    indexReg,               // registre d'index utilisé
            IARG_REG_VALUE, indexReg,               // valeur lors du callback
            IARG_UINT32,    INS_MemoryScale(ins),   // valeur du scale (0 si aucun)
            IARG_UINT32,    INS_MemoryDisplacement(ins),  // déplacement (0 si aucun) 
            CALLBACK_DEBUG
            IARG_END);
    }
}   // sLEA

#if TARGET_IA32
void MISC::taintLEA(TaintManager_Thread *pTmgrTls, REG regDest, UINT32 lenEA, UINT32 lenDest, const TaintDwordPtr &tPtr)
#else
void MISC::taintLEA(TaintManager_Thread *pTmgrTls, REG regDest, UINT32 lenEA, UINT32 lenDest, const TaintQwordPtr &tPtr)
#endif
{
    // Boucle de 0 à (lenEA >> 3)  : extraction octet i de l'addition/soustraction 
    // et affectation à octet i de la destination (sauf si lenDest < leaEA : on arrete avant)
    // octets de (lenEA >> 3) à (lenDest >> 3) mis à zéro si besoin
    
    REGINDEX regDestIndex = getRegIndex(regDest);
    UINT32 regPart = 0;
    UINT32 lastTaintedByte = (lenEA < lenDest) ? (lenEA >> 3) : (lenDest >> 3); 

    // marquage destination
    do
    {
        pTmgrTls->updateTaintRegisterPart(regDestIndex, regPart, std::make_shared<TaintByte>
            (EXTRACT,
            ObjectSource(tPtr),
            ObjectSource(8, regPart)));
    } while (++regPart < lastTaintedByte);

    // démarquage octets forts (si lenDest > lenEA car zeroextend de l'EA)
    while (regPart < (lenDest >> 3))  pTmgrTls->unTaintRegisterPart(regDestIndex, regPart++);
}// taintLEA

///////////
// LEAVE //
///////////

#if TARGET_IA32
void MISC::cLEAVE(INS &ins) 
{
    // LEAVE (32bits) <=> MOV (E)SP, (E)BP + POP (E)BP (POP simulé en MOVMR)
    // par défaut sur 32 bits
    void (*cMOV)() = (AFUNPTR) DATAXFER::sMOV_RR<32>;
    void (*cPOP)() = (AFUNPTR) DATAXFER::sMOV_MR<32>;
    REG regEbp = REG_EBP;
    REG regEsp = REG_ESP;
 
    if (INS_MemoryReadSize(ins) == 2) // sur 16bit : changement en BP et SP
    {
        cMOV = (AFUNPTR) DATAXFER::sMOV_RR<16>;
        cPOP = (AFUNPTR) DATAXFER::sMOV_MR<16>;
        regEbp = REG_BP;
        regEsp = REG_SP;
    }

    INS_InsertCall(ins, IPOINT_BEFORE, cMOV,
        IARG_CALL_ORDER, CALL_ORDER_FIRST,
        IARG_THREAD_ID,
        IARG_UINT32, regEbp,   // registre source = (E)BP
        IARG_UINT32, regEsp,   // registre de destination = (E)SP 
        CALLBACK_DEBUG IARG_END);

    INS_InsertCall(ins, IPOINT_BEFORE, cPOP,
        IARG_CALL_ORDER, CALL_ORDER_LAST,
        IARG_THREAD_ID,
        IARG_REG_VALUE, regEbp, // ATTENTION : valeur d'ESP à ce moment là  = EBP (suite au MOV plus haut) 
        IARG_UINT32,    regEbp, // registre de destination
        CALLBACK_DEBUG IARG_END);
}
#else
void MISC::cLEAVE(INS &ins) 
{
    // LEAVE (64bits) <=> MOV RSP, RBP + POP RBP (POP simulé en MOVMR)
    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) DATAXFER::sMOV_RR<64>,
        IARG_CALL_ORDER, CALL_ORDER_FIRST,
        IARG_THREAD_ID,
        IARG_UINT32, REG_RBP,   // registre source = RBP
        IARG_UINT32, REG_RSP,   // registre de destination = RSP 
        CALLBACK_DEBUG IARG_END);

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) DATAXFER::sMOV_MR<64>,
        IARG_CALL_ORDER, CALL_ORDER_LAST,
        IARG_THREAD_ID,
        IARG_REG_VALUE, REG_RBP, // ATTENTION : valeur d'ESP à ce moment là  = EBP (suite au MOV plus haut)
        IARG_UINT32,    REG_RBP, // registre de destination
        CALLBACK_DEBUG IARG_END);
}
#endif
