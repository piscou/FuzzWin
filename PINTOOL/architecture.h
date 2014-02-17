#pragma once

/**************************************************/
/* fichier définissant les variables différentes  */
/* entre les versions 32bits et 64bits du pintool */
/**************************************************/

namespace ARCHITECTURE
{
/******************************/
/**** ARCHITECTURE 32 bits ****/
/******************************/
#if TARGET_IA32 
// les registres sont découpes en 4 sous registres de 8 bits
#define BYTEPARTS 4
// taille des adresses et des registres généraux entiers : 32bits
#define ADDRLENGTH 32

// liste des registres "entiers" suivis dans le marquage
// en x86, 8 registres de 32bits, 8 registres de 16 bits
enum REGINDEX 
{
    rEAX, rEBX, rECX, rEDX,
    rESI, rEDI, rEBP, rESP,
    rLAST = rESP,
    rINVALID
};

// transformation d'un registre au format PIN
// à un registre utilisé dans le marquage

inline REGINDEX getRegIndex(REG r) 
{
    REGINDEX index = rINVALID;
    switch (r) 
    {
    case REG_EAX:
    case REG_AL:
    case REG_AH:
    case REG_AX:
        index = rEAX;   break;
    case REG_EBX:
    case REG_BL:
    case REG_BH:
    case REG_BX:
        index = rEBX;   break;
    case REG_ECX:
    case REG_CL:
    case REG_CH:
    case REG_CX:
        index = rECX;   break;
    case REG_EDX:
    case REG_DL:
    case REG_DH:
    case REG_DX:
        index = rEDX;   break;
    case REG_ESI:
    case REG_SI:
        index = rESI;   break;
    case REG_EDI:
    case REG_DI:
        index = rEDI;   break;
    case REG_EBP:
    case REG_BP:
        index = rEBP;   break;
    case REG_ESP:
    case REG_SP:
        index = rESP;   break;
    }
    // si registre n'est pas listé ci dessous, retourner rINVALID (invalide)
    return (index); 
}

// taille d'un registre sous le format PIN
inline UINT32 getRegSize(REG r) 
{
    UINT32 size = 0;
    switch (r) 
    {
    case REG_AL:
    case REG_AH:
    case REG_BL:
    case REG_BH:
    case REG_CL:
    case REG_CH:
    case REG_DL:
    case REG_DH:
        size = 1;   break;
    case REG_AX:
    case REG_BX:
    case REG_CX:
    case REG_DX:
    case REG_SI:
    case REG_DI:
    case REG_BP:
    case REG_SP:
        size = 2;   break;
    case REG_EAX:
    case REG_EBX:
    case REG_ECX:
    case REG_EDX:
    case REG_ESI:
    case REG_EDI:
    case REG_EBP:
    case REG_ESP:
        size = 4;   break;
    }
    // si le registre n'est pas référencé, retourner taille nulle
    return (size); 
}

#else   
/******************************/
/**** ARCHITECTURE 64 bits ****/
/******************************/

// les registres sont découpes en 8 sous registres de 8 bits
#define BYTEPARTS 8
// taille des adresses et des registres généraux entiers : 32bits
#define ADDRLENGTH 64

// liste des registres "entiers" suivis dans le marquage
enum REGINDEX 
{
    rRAX, rRBX, rRCX, rRDX, rRSI, rRDI, rRBP, rRSP,
    rR8, rR9, rR10, rR11, rR12, rR13, rR14, rR15,
    rLAST = rR15,
    rINVALID
};

// en 64bits, on dénombre les registres généraux suivants 
// (source : http://asm.developpez.com/faq/?page=fx64_generalites)
// - 16 registres 8 bits « bas » : AL, BL, CL, DL, SIL, DIL, 
//   BPL, SPL, R8B, R9B, R10B, R11B, R12B, R13B, R14B, R15B. 
// - 4 registres 8 bits « haut » : AH, BH, CH, DH
// - 16 registres 16 bits : AX, BX, CX, DX, DI, SI, BP, SP,
//   R8W, R9W, R10W, R11W, R12W, R13W, R14W, R15W. 
// - 16 registres 32 bits : EAX, EBX, ECX, EDX, EDI, ESI, EBP, ESP,
//   R8D, R9D, R10D, R11D, R12D, R13D, R14D, R15D. 
// - 16 registres 64 bits : RAX, RBX, RCX, RDX, RDI, RSI, RBP, RSP, 
//   R8, R9, R10, R11, R12, R13, R14, R15.
inline REGINDEX getRegIndex(REG r) 
{
    REGINDEX index = rINVALID;
    switch (r) 
    {
    case REG_RAX:
    case REG_EAX:
    case REG_AX:
    case REG_AH:
    case REG_AL:
        index = rRAX;   break;
    case REG_RBX:
    case REG_EBX:
    case REG_BX:
    case REG_BH:
    case REG_BL:
        index = rRBX;   break;
    case REG_RCX:
    case REG_ECX:
    case REG_CX:
    case REG_CH:
    case REG_CL:
        index = rRCX;   break;
    case REG_RDX:
    case REG_EDX:
    case REG_DX:    
    case REG_DH:
    case REG_DL:
        index = rRDX;   break;
    case REG_RSI:
    case REG_ESI:
    case REG_SI:
    case REG_SIL:
        index = rRSI;   break;
    case REG_RDI:
    case REG_EDI:
    case REG_DI:
    case REG_DIL:
        index = rRDI;   break;
    case REG_RBP:
    case REG_EBP:
    case REG_BP:
    case REG_BPL:
        index = rRBP;   break;
    case REG_RSP:
    case REG_ESP:
    case REG_SP:
    case REG_SPL:
        index = rRSP;   break;
    case REG_R8:
    case REG_R8D:
    case REG_R8W:
    case REG_R8B:
        index = rR8;    break;
    case REG_R9:
    case REG_R9D:
    case REG_R9W:
    case REG_R9B:
        index = rR9;    break;
    case REG_R10:
    case REG_R10D:
    case REG_R10W:
    case REG_R10B:
        index = rR10;   break;
    case REG_R11:
    case REG_R11D:
    case REG_R11W:
    case REG_R11B:
        index = rR11;   break;
    case REG_R12:
    case REG_R12D:
    case REG_R12W:
    case REG_R12B:
        index = rR12;   break;
    case REG_R13:
    case REG_R13D:
    case REG_R13W:
    case REG_R13B:
        index = rR13;   break;
    case REG_R14:
    case REG_R14D:
    case REG_R14W:
    case REG_R14B:
        index = rR14;   break;
    case REG_R15:
    case REG_R15D:
    case REG_R15W:
    case REG_R15B:
        index = rR15;   break;
    }
    // si registre n'est pas listé ci dessous, retourner rINVALID
    return (index); 
}

// taille d'un registre sous le format PIN
inline UINT32 getRegSize(REG r) 
{
    UINT32 size = 0;
    switch (r) 
    {
    case REG_AL:
    case REG_AH:
    case REG_BL:
    case REG_BH:
    case REG_CL:
    case REG_CH:
    case REG_DL:
    case REG_DH:
    case REG_R8B:
    case REG_R9B:
    case REG_R10B:
    case REG_R11B:
    case REG_R12B:
    case REG_R13B:
    case REG_R14B:
    case REG_R15B:
    case REG_SIL:
    case REG_DIL:
    case REG_BPL:
    case REG_SPL:
        size = 1;   break;
    case REG_AX:
    case REG_BX:
    case REG_CX:
    case REG_DX:
    case REG_SI:
    case REG_DI:
    case REG_BP:
    case REG_SP:
    case REG_R8W:
    case REG_R9W:
    case REG_R10W:
    case REG_R11W:
    case REG_R12W:
    case REG_R13W:
    case REG_R14W:
    case REG_R15W:
        size = 2;   break;
    case REG_EAX:
    case REG_EBX:
    case REG_ECX:
    case REG_EDX:
    case REG_ESI:
    case REG_EDI:
    case REG_EBP:
    case REG_ESP:
    case REG_R8D:
    case REG_R9D:
    case REG_R10D:
    case REG_R11D:
    case REG_R12D:
    case REG_R13D:
    case REG_R14D:
    case REG_R15D:
        size = 4;   break;
    case REG_RAX:
    case REG_RBX:
    case REG_RCX:
    case REG_RDX:
    case REG_RSI:
    case REG_RDI:
    case REG_RBP:
    case REG_RSP:
    case REG_R8:
    case REG_R9:
    case REG_R10:
    case REG_R11:
    case REG_R12:
    case REG_R13:
    case REG_R14:
    case REG_R15:
        size = 8;   break;
    }
    // si le registre n'est pas référencé, retourner 0 (invalide)
    return (size);
}
#endif
} // namespace ARCHITECTURE

// une fois pour toutes
using namespace ARCHITECTURE;