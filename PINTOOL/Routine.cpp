#include "instrumentation.h"
#include "routine.h"
#include "TaintManager.h"

static bool proceedAfterRoutine;

WINDOWS::HANDLE hFile_saved;
void * pBufferRead;
WINDOWS::LPDWORD pBytesReallyRead;

// listes des handles ayant acces au fichier cible, et position de l'offset associé 
std::map<WINDOWS::HANDLE, UINT32> handles;

void INSTRUMENTATION::Image(IMG img, void *v)
{
#if 0
    // Walk through the symbols in the symbol table.
    //
    for (SYM sym = IMG_RegsymHead(img); SYM_Valid(sym); sym = SYM_Next(sym))
    {
        std::string undFuncName = PIN_UndecorateSymbolName(SYM_Name(sym), UNDECORATION_NAME_ONLY);

        //  Find the CreateFileW() function.
        if (undFuncName == "CreateFileW")
        {
            RTN RTN_CreateFileW = RTN_FindByAddress(IMG_LowAddress(img) + SYM_Value(sym));
           
            string dllName = IMG_Name(img);
            if (RTN_Valid(RTN_CreateFileW))
            {
                RTN_Open(RTN_CreateFileW);
                
                RTN_InsertCall(RTN_CreateFileW, IPOINT_BEFORE, (AFUNPTR) ROUTINE::sCreateFileW_Before,
                    IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 0 : nom du fichier
                    IARG_FUNCARG_ENTRYPOINT_VALUE, 1, // argument 1 : accès désiré
                    IARG_END);

                RTN_InsertCall(RTN_CreateFileW, IPOINT_AFTER, (AFUNPTR) ROUTINE::sCreateFile_After,
                    IARG_FUNCRET_EXITPOINT_VALUE, // retour : handle du fichier ouvert
                    IARG_END);
            
                RTN_Close(RTN_CreateFileW);
            }
        }
    }
#endif

    if (IMG_Name(img).find("ntdll.dll") != std::string::npos)
    {
        _LOGDEBUG(IMG_Name(img));
        RTN RTN_ReadFile = RTN_FindByName(img, "ReadFile");
        RTN RTN_OpenFile = RTN_FindByName(img, "OpenFile");  // kernel32, non recommandé (utiliser createFileA ou W à la place)
        RTN RTN_CreateFileA = RTN_FindByName(img, "CreateFileA");  
        RTN RTN_CreateFileW = RTN_FindByName(img, "CreateFileW");  
        RTN RTN_SetFilePointer = RTN_FindByName(img, "SetFilePointer");

        if (RTN_Valid(RTN_ReadFile))
        {
            RTN_Open(RTN_ReadFile);
            RTN_InsertCall(RTN_ReadFile, IPOINT_BEFORE, (AFUNPTR) ROUTINE::sReadFile_Before,
                IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 0 : handle du fichier à lire
                IARG_FUNCARG_ENTRYPOINT_VALUE, 1, // argument 1 : buffer de stockage des données
                //IARG_FUNCARG_ENTRYPOINT_VALUE, 2, // argument 2 : nb octets a lire
                IARG_FUNCARG_ENTRYPOINT_VALUE, 3, // argument 3 : pointeur vers nb octets lus
                IARG_END);

            RTN_InsertCall(RTN_ReadFile, IPOINT_AFTER, (AFUNPTR) ROUTINE::sReadFile_After,
                IARG_FUNCRET_EXITPOINT_VALUE, // retour : VRAI si lecture réussie
                IARG_END);
            RTN_Close(RTN_ReadFile);
        }

        if (RTN_Valid(RTN_OpenFile))
        {
            RTN_Open(RTN_OpenFile);
            RTN_InsertCall(RTN_OpenFile, IPOINT_BEFORE, (AFUNPTR) ROUTINE::sOpenFile_Before,
                IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 0 : nom du fichier
                IARG_FUNCARG_ENTRYPOINT_VALUE, 2, // argument 2 : style (type d'ouverture de fichier)
                IARG_END);

            RTN_InsertCall(RTN_OpenFile, IPOINT_AFTER, (AFUNPTR) ROUTINE::sOpenFile_After,
                IARG_FUNCRET_EXITPOINT_VALUE, // retour : HFILE mais sera casté en handle
                IARG_END);
            RTN_Close(RTN_OpenFile);
        }

        if (RTN_Valid(RTN_CreateFileA))
        {
            RTN_Open(RTN_CreateFileA);
            RTN_InsertCall(RTN_CreateFileA, IPOINT_BEFORE, (AFUNPTR) ROUTINE::sCreateFileA_Before,
                IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 0 : nom du fichier
                IARG_FUNCARG_ENTRYPOINT_VALUE, 1, // argument 1 : accès désiré
                IARG_END);

            RTN_InsertCall(RTN_CreateFileA, IPOINT_AFTER, (AFUNPTR) ROUTINE::sCreateFile_After,
                IARG_FUNCRET_EXITPOINT_VALUE, // retour : handle du fichier ouvert
                IARG_END);
            RTN_Close(RTN_CreateFileA);
        }

        if (RTN_Valid(RTN_CreateFileW))
        {
            RTN_Open(RTN_CreateFileW);

            RTN_InsertCall(RTN_CreateFileW, IPOINT_BEFORE, (AFUNPTR) ROUTINE::sCreateFileW_Before,
                IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 0 : nom du fichier
                IARG_FUNCARG_ENTRYPOINT_VALUE, 1, // argument 1 : accès désiré
                IARG_END);

            RTN_InsertCall(RTN_CreateFileW, IPOINT_AFTER, (AFUNPTR) ROUTINE::sCreateFile_After,
                IARG_FUNCRET_EXITPOINT_VALUE, // retour : handle du fichier ouvert
                IARG_END);

            RTN_Close(RTN_CreateFileW);
        }

        if (RTN_Valid(RTN_SetFilePointer))
        {
            RTN_Open(RTN_SetFilePointer);
            RTN_InsertCall(RTN_SetFilePointer, IPOINT_BEFORE, (AFUNPTR) ROUTINE::sSetFilePointer_Before,
                IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 0 : handle du fichier
                IARG_FUNCARG_ENTRYPOINT_VALUE, 1, // argument 0 : handle du fichier
                IARG_FUNCARG_ENTRYPOINT_VALUE, 3, // argument 0 : handle du fichier
                IARG_END);

            RTN_InsertCall(RTN_SetFilePointer, IPOINT_AFTER, (AFUNPTR) ROUTINE::sSetFilePointer_After,
                IARG_FUNCRET_EXITPOINT_VALUE, // retour : nouvelle position
                IARG_END);

            RTN_Close(RTN_SetFilePointer);
        }
    }
}


//****** OPENFILE ******//

void ROUTINE::sOpenFile_Before(WINDOWS::LPCSTR pFileName, UINT style)
{
#if 0
    isInsideRoutine = true; // stop à l'instrumentation niveau instruction

    // si ouverture avec le flag OF_WRITE (0x1), ne pas instrumenter
    if (style & 1) return;

    // vérification du nom de fichier ouvert pour comparaison avec le fichier suivi
    if (strstr(pFileName, KnobInputFile.Value().c_str()) != nullptr) 
    { 
        proceedAfterRoutine = true;
        _LOGDEBUG("*** OpenFile Before FICHIER CIBLE");
    }
    else  _LOGDEBUG("*** OpenFile Before Device non suivi");
#endif
}

void ROUTINE::sOpenFile_After(WINDOWS::HFILE hFile)
{
    if (!proceedAfterRoutine) return;

    // Sauvegarde du handle dans la map, avec offset positionné au début du fichier
    handles.insert(pair<WINDOWS::HANDLE, UINT32>((WINDOWS::HANDLE) hFile, 0));

    _LOGDEBUG("Fichier cible OUVERT, handle = " << hFile);
    //isInsideRoutine = false; // reprise de l'instrumentation niveau instruction
    proceedAfterRoutine = false;          
}

//****** READFILE ******//

void ROUTINE::sReadFile_Before(WINDOWS::HANDLE hFile, void* buffer, WINDOWS::LPDWORD pBytesRead)
{
    //isInsideRoutine = true; // stop à l'instrumentation niveau instruction

    if (handles.find(hFile) != handles.end()) // si handle suivi (y compris stdin)
    {
        proceedAfterRoutine = true;
        _LOGDEBUG("*** ReadFile Before FICHIER CIBLE");
        // sauvegarde des pointeurs fournis pour traitement après la procédure
        hFile_saved = hFile;    // handle du fichier lu
        pBufferRead = buffer;   // buffer de remplissage des données
        pBytesReallyRead = pBytesRead; // nombre d'octets qui auront été lus
    }
}

void ROUTINE::sReadFile_After(WINDOWS::BOOL hasSucceeded)
{
    if (hasSucceeded && proceedAfterRoutine)
    {
        _LOGDEBUG("READFILE AFTER REUSSI !!! nb octets lus " << *pBytesReallyRead);
        UINT32 startOffset = handles.at(hFile_saved); // ancienne position dans le fichier
        
        // marquage de la mémoire
        pTmgrGlobal->createNewSourceTaintBytes((ADDRINT) pBufferRead, *pBytesReallyRead, startOffset);

        // mise à jour de l'offset de lecture
        handles.at(hFile_saved) += *pBytesReallyRead;

        // des données ont été lues dans le fichier : on peut commencer l'instrumentation
        beginInstrumentation = true;
    }
    
   // isInsideRoutine = false; // reprise de l'instrumentation niveau instruction
    proceedAfterRoutine = false; 
}

//****** CREATEFILE ******//

void ROUTINE::sCreateFileA_Before(WINDOWS::LPCSTR pFileName, WINDOWS::DWORD desiredAccess)
{
#if 0
    isInsideRoutine = true; // stop à l'instrumentation niveau instruction

    if (desiredAccess = GENERIC_WRITE) return;  // pas d'instrumentation possible alors

    // vérification du nom de fichier ouvert pour comparaison avec le fichier suivi
    if (strstr(pFileName, KnobInputFile.Value().c_str()) != nullptr) 
    { 
        proceedAfterRoutine = true;
        _LOGDEBUG("*** CreateFileA Before FICHIER CIBLE");
    }
    else  _LOGDEBUG("*** CreateFileA Before Device non suivi");
#endif
}

//void ROUTINE::sCreateFileW_Before(WINDOWS::LPCWSTR pFileName, WINDOWS::DWORD desiredAccess)
void ROUTINE::sCreateFileW_Before(ADDRINT arg0, ADDRINT arg1)
{
#if 0
    isInsideRoutine = true; // stop à l'instrumentation niveau instruction

    WINDOWS::DWORD desiredAccess = static_cast<WINDOWS::DWORD>(arg1);
    WINDOWS::LPCWSTR pFileName = reinterpret_cast<WINDOWS::LPCWSTR>(arg0);

    if (desiredAccess == GENERIC_WRITE) return;  // pas d'instrumentation possible alors

    std::wstring wideFileNameOpened(pFileName);
    std::wstring wideFileNameToFollow(KnobInputFile.Value().begin(), KnobInputFile.Value().end());

    // vérification du nom de fichier ouvert pour comparaison avec le fichier suivi
    if (wideFileNameToFollow.find(wideFileNameOpened) != std::wstring::npos) 
    { 
        proceedAfterRoutine = true;
        _LOGDEBUG("*** CreateFileW Before FICHIER CIBLE");
    }
#endif
}

void ROUTINE::sCreateFile_After(ADDRINT rtnReturn)
{
#if 0
    if (!proceedAfterRoutine) return;
    
    WINDOWS::HANDLE hFile = reinterpret_cast<WINDOWS::HANDLE>(rtnReturn);

    // Sauvegarde du handle dans la map, avec offset positionné au début du fichier
    handles.insert(pair<WINDOWS::HANDLE, UINT32>(hFile, 0));

    _LOGDEBUG("Fichier cible OUVERT, handle = " << reinterpret_cast<UINT32>(hFile));
    isInsideRoutine = false; // reprise de l'instrumentation niveau instruction
    proceedAfterRoutine = false;  
#endif
}

//****** SETFILEPOINTER ******//

void ROUTINE::sSetFilePointer_Before(ADDRINT arg0, ADDRINT arg1, ADDRINT arg3)
{
#if 0
    isInsideRoutine = true; // stop à l'instrumentation niveau instruction
    
    WINDOWS::HANDLE hFile = reinterpret_cast<WINDOWS::HANDLE>(arg0);

    if (handles.find(hFile) != handles.end()) // si handle suivi 
    {
        proceedAfterRoutine = true;
        _LOGDEBUG("*** SetFilePointer Before FICHIER CIBLE");
        // sauvegarde du handle fourni pour traitement après la procédure
        hFile_saved = hFile;    
    }
#endif
}

void ROUTINE::sSetFilePointer_After(ADDRINT rtnReturn)
{
#if 0
    if (!proceedAfterRoutine) return;
    
    WINDOWS::DWORD positionAfterMove = static_cast<WINDOWS::DWORD>(rtnReturn);
    _LOGDEBUG("*** SetFilePointer AFter nouvelle position " << positionAfterMove);

    // mise à jour de l'offset de lecture
    handles.at(hFile_saved) += positionAfterMove;

    isInsideRoutine = false; // reprise de l'instrumentation niveau instruction
    proceedAfterRoutine = false; 
#endif
}

#if 0
    if (RTN_Valid(mallocRtn))
    {
        RTN_Open(mallocRtn);
        RTN_InsertCall(mallocRtn, IPOINT_BEFORE, (AFUNPTR) ROUTINE::beforeMalloc,
            IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // 1er argument = taille
            CALLBACK_DEBUG IARG_END);

        RTN_InsertCall(mallocRtn, IPOINT_AFTER, (AFUNPTR) ROUTINE::afterMalloc,
            IARG_FUNCRET_EXITPOINT_VALUE, // valeur retour = adresse de la mémoire
            CALLBACK_DEBUG IARG_END);
        
        RTN_Close(mallocRtn);
    }
    if (RTN_Valid(freeRtn))
    {
        RTN_Open(freeRtn);
        RTN_InsertCall(
            freeRtn,
            IPOINT_BEFORE, (AFUNPTR) ROUTINE::free,
            IARG_FUNCARG_ENTRYPOINT_VALUE, 0, // argument 1 : adresse à libérer
            CALLBACK_DEBUG IARG_END);
        RTN_Close(freeRtn);
    }
    
void ROUTINE::beforeMalloc(ADDRINT size ADDRESS_DEBUG)
{
    _LOGDEBUG(std::hex << insAddress << " Appel Malloc octets demandés " << size);
}

void ROUTINE::afterMalloc(ADDRINT bufferAddress ADDRESS_DEBUG)
{
    _LOGDEBUG(std::hex << insAddress << " Retour Malloc addresse buffer " << bufferAddress);
}

void ROUTINE::free(ADDRINT bufferAddress ADDRESS_DEBUG)
{
    _LOGDEBUG(std::hex << insAddress << "Free addresse libérée " << bufferAddress);
}



// verification des adresses de retour des fonctions
// sauvegarde de l'adresse de retour à l'entrée de la fonction
// et comparaison lors de la sortie de la fonction

// source : BINARY INSTRUMENTATION FOR SECURITY PROFESSIONALS
// GAL DISKIN / INTEL (présentation au BlackHat 2011)

std::stack<protectedAddresses> protect;

VOID ROUTINE::RtnEntry(ADDRINT esp, ADDRINT addr) 
{ 
    protectedAddresses pa;
    pa.espAddress = esp; 
    pa.returnValue = *((ADDRINT *)esp); 
    //protect.push(pa);
    pTmgr->pushProtectedAdresses(pa);
}

VOID ROUTINE::RtnExit(ADDRINT esp, ADDRINT addr) 
{
    //if (protect.empty()) return;
    
    if (pTmgr->isProtectedAddressesEmpty()) return;
    protectedAddresses pa = pTmgr->getProtectedAdresses();
  
    ADDRINT cur_val = (*((ADDRINT *)pa.espAddress));
    if (pa.returnValue != cur_val) 
    {
        _LOGDEBUG( "Overwrite at: " << pa.espAddress << " old value: " \
            << pa.returnValue << " new value: " << cur_val);
    }
    else
    {
        _LOGDEBUG("Retour fonction " << addr << "tout va bien");
    }
}
#endif