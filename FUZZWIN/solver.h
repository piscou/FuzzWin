#pragma once
#include "fuzzwin.h"

static const std::string solverConfig(
    "(set-option :auto-config false)"   \
    "(set-option :produce-models true)" \
    "(set-option :print-success false)" \
    "(set-option :relevancy 0)"         \
    "(set-option :smtlib2_compliant true)"  \
    "(set-logic QF_AUFBV)");

bool	createSolverProcess(const std::string &solverPath);
std::string	getModelFromSolver();
bool    checkSatFromSolver();
bool	sendToSolver(const std::string &data);
