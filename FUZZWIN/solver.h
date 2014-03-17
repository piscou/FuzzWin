#pragma once
#include "fuzzwin.h"

bool	createSolverProcess(const std::string &solverPath);
std::string	getModelFromSolver();
bool    checkSatFromSolver();
bool	sendToSolver(const std::string &data);
