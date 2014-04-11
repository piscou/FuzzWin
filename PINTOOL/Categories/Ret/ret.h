#pragma once
#include <TaintEngine\TaintManager.h>

namespace RET 
{
// CALLBACKS
void cRET(INS &ins);

// SIMULATE 
void sRET(ADDRINT insAddress, ADDRINT espAddress);
} // namespace CALL
