#pragma once
#include "fuzzwin.h"
#include "CInput.h"

int         sendArgumentsToPintool(const std::string &command);
std::string callFuzzwin(CInput* pInput);
int         createNamedPipePintool();