#pragma once
#include "pintool.h" 

namespace CALL 
{
// CALLBACKS
void cCALL(INS &ins);

// SIMULATE 
void sCALL(ADDRINT callingIp, UINT32 size);
} // namespace CALL
