#pragma once
#include <TaintEngine\TaintManager.h>

namespace RET 
{
// CALLBACKS
void cRET(INS &ins, bool isFarRet);

// SIMULATE 
void sRET(ADDRINT insAddress, ADDRINT espAddress);
} // namespace CALL
