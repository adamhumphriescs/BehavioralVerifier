//===-- ConstructSolverChain.cpp ------------------------------------++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

/*
 * This file groups declarations that are common to both KLEE and Kleaver.
 */
#include "klee/Common.h"
#include "klee/CommandLine.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "klee/CommandLine.h"
#include "tase_interp.h"

namespace klee {
Solver *constructSolverChain(Solver *coreSolver,
                             std::string querySMT2LogPath,
                             std::string baseSolverQuerySMT2LogPath,
                             std::string queryKQueryLogPath,
                             std::string baseSolverQueryKQueryLogPath) {
  Solver *solver = coreSolver;

  LOG_TASE("Constructing Solver Chain:\n");
  
  if (queryLoggingOptions.isSet(SOLVER_KQUERY)) {
    LOG_TASE("\tKQueryLoggingSolver\n");
    solver = createKQueryLoggingSolver(solver, baseSolverQueryKQueryLogPath,
                                   MinQueryTimeToLog);
    klee_message("Logging queries that reach solver in .kquery format to %s\n",
                 baseSolverQueryKQueryLogPath.c_str());
  }

  if (queryLoggingOptions.isSet(SOLVER_SMTLIB)) {
    LOG_TASE("\tSMTLLIBLoggingSolver\n");
    solver = createSMTLIBLoggingSolver(solver, baseSolverQuerySMT2LogPath,
                                       MinQueryTimeToLog);
    klee_message("Logging queries that reach solver in .smt2 format to %s\n",
                 baseSolverQuerySMT2LogPath.c_str());
  }

  if (UseAssignmentValidatingSolver) {
    LOG_TASE("\tAssignmentValidatingSolver\n");
    solver = createAssignmentValidatingSolver(solver);
  }
    
  if (UseFastCexSolver) {
    LOG_TASE("\tFastCexSolver\n");
    solver = createFastCexSolver(solver);
  }
  if (UseCexCache) {
    LOG_TASE("\tCexCachingSolver\n");
    solver = createCexCachingSolver(solver);
  }
  if (UseCache) {
    LOG_TASE("\tCachingSolver\n");
    solver = createCachingSolver(solver);
  }
  /* if (UseTrivialEqSolver) 
    solver = createTrivialEqualitySolver(solver);
  */
  
  if (UseCanonicalization) {
    printf("\tCononicalizationSolver\n");
    solver = createCanonicalSolver(solver);
  }
  if (UseIndependentSolver) {
    printf("\tIndependetSolver\n");
    solver = createIndependentSolver(solver, UseLegacyIndependentSolver);
  }
  if (DebugValidateSolver) {
    printf("\tValidatingSolver\n");
    solver = createValidatingSolver(solver, coreSolver);
  }
  if (queryLoggingOptions.isSet(ALL_KQUERY)) {
    LOG_TASE("\tKQueryLoggingSolver\n");    
    solver = createKQueryLoggingSolver(solver, queryKQueryLogPath,
                                       MinQueryTimeToLog);
    klee_message("Logging all queries in .kquery format to %s\n",
                 queryKQueryLogPath.c_str());
  }

  if (queryLoggingOptions.isSet(ALL_SMTLIB)) {
    LOG_TASE("\tSMTLIBLoggingSolver\n");    
    solver =
        createSMTLIBLoggingSolver(solver, querySMT2LogPath, MinQueryTimeToLog);
    klee_message("Logging all queries in .smt2 format to %s\n",
                 querySMT2LogPath.c_str());
  }
  if (DebugCrossCheckCoreSolverWith != NO_SOLVER) {
    LOG_TASE("\tDebugCrossCheckCoreSolver\n");
    Solver *oracleSolver = createCoreSolver(DebugCrossCheckCoreSolverWith);
    solver = createValidatingSolver(/*s=*/solver, /*oracle=*/oracleSolver);
  }

  return solver;
}
}
