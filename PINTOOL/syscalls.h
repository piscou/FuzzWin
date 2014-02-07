#pragma once
#include "pintool.h"
#include <map>

// valeur utilisée pour faire un fseek avec le syscall SetInformationFile
#define FilePositionInformation         0xe     
// valeur utilisée par ReadFile pour spécifier de lire 
// à partir de l'offset actuel (source : Windows Driver Kit, wdm.h)
#define FILE_USE_FILE_POINTER_POSITION  0xfffffffe  

// typedefs utiles pour la partie syscalls
// obligation de redifinir ces structures qui font partie 
// pour la plupart de wdm.h (driver kit)
typedef WINDOWS::HANDLE HANDLE;
typedef HANDLE *PHANDLE;

typedef struct _UNICODE_STRING 
{
    WINDOWS::USHORT Length;
    WINDOWS::USHORT MaximumLength;
    WINDOWS::PWSTR  Name;
} UNICODE_STRING, *PUNICODE_STRING;

typedef struct _OBJECT_ATTRIBUTES 
{
    WINDOWS::ULONG      Length;
    WINDOWS::HANDLE     RootDirectory;
    PUNICODE_STRING     ObjectName;
    WINDOWS::ULONG      Attributes ;
    WINDOWS::PVOID      SecurityDescriptor;
    WINDOWS::PVOID      SecurityQualityOfService;
} OBJECT_ATTRIBUTES, *POBJECT_ATTRIBUTES;

typedef struct _IO_STATUS_BLOCK 
{
    union 
    {
        WINDOWS::NTSTATUS   Status;
        WINDOWS::PVOID      Pointer;
    };
    WINDOWS::ULONG_PTR      Information;
} IO_STATUS_BLOCK, *PIO_STATUS_BLOCK;

typedef struct _FILE_POSITION_INFORMATION
{
    WINDOWS::LARGE_INTEGER  CurrentByteOffset;
} FILE_POSITION_INFORMATION, *PFILE_POSITION_INFORMATION;

class Syscall_Data
{
public:
    /***** COMMUN A TOUS LES SYSCALLS *****/
    ADDRINT syscallNumber;
    // listes des handles de fichier  du fichier cible et offset associé (32bits )
    std::map<HANDLE, UINT32> listOfFileHandles;
    // listes des handles de section du fichier cible et offset associé (32bits )
    std::vector<HANDLE>      listOfSectionHandles;

    /***** ReadFile *****/
    // pointeur vers structure d'informations remplie par le syscall
    PIO_STATUS_BLOCK pInfos; 
    // adresse du buffer qui recevra les données après lecture
    void *pBuffer; 
    // offset de lecture AVANT le syscall; vaut normalement l'offset actuel
    // sauf si l'argument 7 de ReadFile en spécifie un autre
    // dans le cas *** SetInformationFile *** = l'offset à fixer
    UINT32 offset; 

    /**** OpenFile & CreateFile & CreateSection *****/
    // pointeur vers handle du fichier après ouverture, ou de la section après création
    PHANDLE pHandle;

    /***** Close & SetInformationFile ***/
    // handle du fichier à traiter, ou de la section (pour Close)
    HANDLE hFile, hSection;

    /**** MapViewOfSection *****/
    // pointeur vers pointeur de l'adresse de base de la section
    void** ppBaseAddress;
    // pointeur vers l'offset de la vue par rapport au début de la section
    WINDOWS::PLARGE_INTEGER pOffsetFromStart;
    // pointeur vers taille de la vue
    WINDOWS::PSIZE_T pViewSize;
};

// codes définissant le type d'OS 32bits pour la détermination des 
// numéros d'appels systèmes, inspiré de l'exemple fourni sur MSDN
// http://msdn.microsoft.com/en-us/library/ms724429(v=vs.85).aspx
// pour les OS 64bits, les numéros des syscalls sont identiques
// quelque soit la version de Windows
enum OSTYPE 
{
    HOST_2000,
    HOST_XP,
    HOST_2003,

    HOST_VISTA_SP0, // pour cette version, le syscall 'setinformationfile' n'est pas le meme que pour les autres SP...
    HOST_VISTA,
    HOST_2008 = HOST_VISTA,   // les index des syscalls sont les mêmes
    HOST_2008_R2 = HOST_2008, // les index des syscalls sont les mêmes
  
    HOST_SEVEN,
    
    HOST_8_0,
    HOST_2012 = HOST_8_0,   // a priori ce sont les memes
    
    HOST_8_1,
    HOST_2012_R2 = HOST_8_1,// a priori ce sont les memes
    
    HOST_WOW64_OR_64BITS,
    HOST_UNSUPPORTED,
    HOST_END = HOST_UNSUPPORTED
};

// types de syscalls qui sont suivis dans le pintool
enum INDEX_SYSCALL 
{
    INDEX_NTCLOSE,
    INDEX_NTCREATEFILE,
    INDEX_NTCREATESECTION,
    INDEX_NTMAPVIEWOFSECTION,
    INDEX_NTOPENFILE,
    INDEX_NTREADFILE,
    INDEX_NTSETINFORMATIONFILE,
    INDEX_SYSCALLS_END
};

// définition des numéros des appels systèmes selon l'OS
// source : http://j00ru.vexillium.org/ntapi/
// mis à jour avec Windows 8.1, le 03/01/2014
static const UINT32 syscallTable[HOST_END][INDEX_SYSCALLS_END] = 
{
    // NtClose, NtCreateFile, NtCreateSection, NtMapViewOfSection, NtOpenFile, NtReadFile, NtSetInformationFile  
    {0x0018, 0x0020, 0x002b, 0x005d, 0x0064, 0x00a1, 0x00c2}, // Windows 2000
    {0x0019, 0x0025, 0x0032, 0x006c, 0x0074, 0x00b7, 0x00e0}, // Windows XP
    {0x001b, 0x0027, 0x0034, 0x0071, 0x007a, 0x00bf, 0x00e9}, // Windows 2003 server
    {0x0030, 0x003c, 0x004b, 0x00b1, 0x00ba, 0x0102, 0x0131}, // Vista SPO (NtSetInformationFile Différent)
    {0x0030, 0x003c, 0x004b, 0x00b1, 0x00ba, 0x0102, 0x012d}, // Windows 2008 server ou Vista 
    {0x0032, 0x0042, 0x0054, 0x00a8, 0x00b3, 0x0111, 0x0149}, // Windows Seven
    {0x0174, 0x0163, 0x0150, 0x00f3, 0x00e8, 0x0087, 0x004e}, // Windows 8.0
    {0x0179, 0x0168, 0x0154, 0x00f6, 0x00eb, 0x008a, 0x0051}, // Windows 8.1
    {0x000c, 0x0052, 0x0047, 0x0025, 0x0030, 0x0003, 0x0024}  // 64 bits, y compris WOW64. A REVOIR CAR DIFFERENTS FINALEMENT A PARTIR DE 8 et 8.1!!!!!
};

// prototype des fonctions
namespace SYSCALLS 
{
    void defineSyscallsNumbers();
    std::string unicodeToAscii(const std::wstring &input);
    void syscallEntry(THREADID tid, CONTEXT *ctxt, SYSCALL_STANDARD std, void *v);
    void syscallExit (THREADID tid, CONTEXT *ctxt, SYSCALL_STANDARD std, void *v);
}
