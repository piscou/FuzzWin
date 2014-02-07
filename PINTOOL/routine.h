#pragma once
#include "pintool.h"

namespace ROUTINE
{
// Save address to protect on entry to function 
//void RtnEntry(ADDRINT esp, ADDRINT addr);
// check if return address was overwritten
//void RtnExit(ADDRINT esp, ADDRINT addr);

//void beforeMalloc(ADDRINT size ADDRESS_DEBUG);
//void afterMalloc(ADDRINT bufferAddress ADDRESS_DEBUG);
//void free(ADDRINT bufferAddress ADDRESS_DEBUG);

/* SetFilePointer (Kernel32.dll) // en entrée seul le handle nous intéresse, en sortie la nouvelle position
DWORD WINAPI SetFilePointer(
  _In_         HANDLE hFile,
  _In_         LONG lDistanceToMove,
  _Inout_opt_  PLONG lpDistanceToMoveHigh,
  _In_         DWORD dwMoveMethod
);
*/
//void sSetFilePointer_Before(WINDOWS::HANDLE hFile);
void sSetFilePointer_Before(ADDRINT arg0, ADDRINT arg1, ADDRINT arg3);
// void sSetFilePointer_After (WINDOWS::DWORD positionAfterMove);
void sSetFilePointer_After (ADDRINT rtnReturn);

/* OpenFile (Kernel32.dll), moins utilisé que CreateFileA/W. Retour HFILE (int) mais en fait c'est un handle
WINDOWS::HFILE WINAPI OpenFile(
    _In_    LPCSTR lpFileName,
    _Inout_ LPOFSTRUCT lpReOpenBuff,
    _In_    UINT uStyle
);
*/
void sOpenFile_Before(WINDOWS::LPCSTR pFileName, UINT style);
void sOpenFile_After (WINDOWS::HFILE hFile);

/* CreateFile (Kernel32.dll) avec 2 versions Unicode(W) et Ansi(A).
en entrée : nom de fichier et acces (seul la lecture nous intéresse)
en sortie : le handle du fichier ouvert
HANDLE WINAPI CreateFileA/W(
    _In_ LPC(W)STR lpFileName,
    _In_ DWORD dwDesiredAccess,
    _In_ DWORD dwShareMode,
    _In_opt_ LPSECURITY_ATTRIBUTES lpSecurityAttributes,
    _In_ DWORD dwCreationDisposition,
    _In_ DWORD dwFlagsAndAttributes,
    _In_opt_ HANDLE hTemplateFile
    );
*/
void sCreateFileA_Before(WINDOWS::LPCSTR pFileName,  WINDOWS::DWORD desiredAccess);
//void sCreateFileW_Before(WINDOWS::LPCWSTR pFileName, WINDOWS::DWORD desiredAccess);
void sCreateFileW_Before(ADDRINT arg0, ADDRINT arg1);

//void sCreateFile_After(WINDOWS::HANDLE hFile);
void sCreateFile_After(ADDRINT rtnReturn);

/* ReadFile (Kernel32.dll). Source MSDN (retoune VRAI si l'appel a réussi)
BOOL WINAPI ReadFile(
  _In_         HANDLE hFile,    
  _Out_        LPVOID lpBuffer, 
  _In_         DWORD nNumberOfBytesToRead, 
  _Out_opt_    LPDWORD lpNumberOfBytesRead,
  _Inout_opt_  LPOVERLAPPED lpOverlapped
);
*/
void sReadFile_Before
    (WINDOWS::HANDLE hFile, void* buffer, WINDOWS::LPDWORD pBytesRead);
void sReadFile_After(WINDOWS::BOOL hasSucceeded);
}