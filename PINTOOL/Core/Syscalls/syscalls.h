#pragma once
#include <TaintEngine\TaintManager.h>
#include <map>

// les types d'OS supportés sont dans un fichier commun pintool / algo SAGE
#include "../ALGORITHME/osType.h"

// valeur utilisée pour faire un fseek avec le syscall SetInformationFile
#define FilePositionInformation         0xe     
// valeur utilisée par ReadFile pour spécifier de lire 
// à partir de l'offset actuel (source : Windows Driver Kit, wdm.h)
#define FILE_USE_FILE_POINTER_POSITION  0xfffffffe  

// typedefs "C-style" utiles pour la partie syscalls
// obligation de redifinir ces structures qui font partie 
// pour la plupart de wdm.h (driver kit)
extern "C"
{
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

    /** Partie spécigfique NtQueryObject **/
    enum OBJECT_INFORMATION_CLASS
    { 
        ObjectBasicInformation  = 0,
        ObjectTypeInformation   = 2
    };

    struct PUBLIC_OBJECT_TYPE_INFORMATION 
    {
        UNICODE_STRING TypeName;
        WINDOWS::ULONG Reserved[22];
    };

    // permet de récupérer l'adresse de la fonction NtQueryObject (NtDll.dll)
    typedef WINDOWS::NTSTATUS (NTAPI* t_NtQueryObject)(
        HANDLE Handle, 
        OBJECT_INFORMATION_CLASS Info, 
        WINDOWS::PVOID Buffer,
        WINDOWS::ULONG BufferSize, 
        WINDOWS::PULONG ReturnLength);

} // extern "C"

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
static const UINT32 syscallTable[HOST_END][INDEX_SYSCALLS_END] = 
{
    // dans l'ordre : 
    // NtClose, NtCreateFile, NtCreateSection, NtMapViewOfSection,
    // NtOpenFile, NtReadFile, NtSetInformationFile  
    // 1) OS 32bits
    {0x0018, 0x0020, 0x002b, 0x005d, 0x0064, 0x00a1, 0x00c2}, // Windows 2000
    {0x0019, 0x0025, 0x0032, 0x006c, 0x0074, 0x00b7, 0x00e0}, // Windows XP
    {0x001b, 0x0027, 0x0034, 0x0071, 0x007a, 0x00bf, 0x00e9}, // Windows 2003 server
    {0x0030, 0x003c, 0x004b, 0x00b1, 0x00ba, 0x0102, 0x0131}, // Vista SP0
    {0x0030, 0x003c, 0x004b, 0x00b1, 0x00ba, 0x0102, 0x012d}, // Windows 2008 server ou Vista 
    {0x0032, 0x0042, 0x0054, 0x00a8, 0x00b3, 0x0111, 0x0149}, // Windows Seven
    {0x0174, 0x0163, 0x0150, 0x00f3, 0x00e8, 0x0087, 0x004e}, // Windows 8.0
    {0x0179, 0x0168, 0x0154, 0x00f6, 0x00eb, 0x008a, 0x0051}, // Windows 8.1
    // 2) OS 64bits
    {0x000c, 0x0052, 0x0047, 0x0025, 0x0030, 0x0003, 0x0024},  // Windows XP ? Seven en x64
    {0x000d, 0x0053, 0x0048, 0x0026, 0x0031, 0x0004, 0x0025},  // Windows 8 x64
    {0x000e, 0x0054, 0x0049, 0x0027, 0x0032, 0x0005, 0x0026}   // Windows 8.1 x64};
};

// prototype des fonctions
namespace SYSCALLS 
{
    void defineSyscallsNumbers(OSTYPE osVersion);
    std::string unicodeToAscii(const std::wstring &input);
    void syscallEntry(THREADID tid, CONTEXT *ctxt, SYSCALL_STANDARD std, void *v);
    void syscallExit (THREADID tid, CONTEXT *ctxt, SYSCALL_STANDARD std, void *v);
}

// variable globale type d'OS hote. Sert à déterminer les numéros de syscalls
extern OSTYPE           g_osType;
// adresse de la fonction NtQueryObject (NtDll.dll)
extern t_NtQueryObject  g_AddressOfNtQueryObject;