#pragma once
#include "pintool.h" 

namespace RET 
{
// CALLBACKS
void cRET(INS &ins);

// SIMULATE 
void sRET(ADDRINT insAddress, ADDRINT espAddress);
} // namespace CALL
