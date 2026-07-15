/*
 * This header groups command line options declarations and associated data
 * that is common for klee and kleaver.
 */

#ifndef KLEE_COMMANDLINE_H
#define KLEE_COMMANDLINE_H

#include "klee/Config/config.h"

#include "llvm/ADT/ArrayRef.h"
#include "llvm/Support/CommandLine.h"

//Tase Types
enum runType : int {INTERP_ONLY, MIXED};
//enum TASETestType : int {EXPLORATION, VERIFICATION};
enum class VerTestType : uint8_t { EXPLORATION, TRAIN, REPLAY, VERIFY, SINGLEMSGVER };
enum class TASETrainType : uint8_t { ML, CLUSTER };
enum class TASEExplorationType : int {DFS, BFS, ML, ED};

enum PoisonSize : uint8_t { WORD = 2, DWORD = 4 };
enum SIMDType : uint32_t { XMM = 128, YMM = 256, ZMM = 512 };

namespace klee {
  //TASE args
  extern llvm::cl::opt<runType> execMode;
  extern llvm::cl::opt<TASEExplorationType> explorationType;
  extern llvm::cl::opt<PoisonSize> poisonSize;
  extern llvm::cl::opt<SIMDType> simdType;
  extern llvm::cl::opt<std::string> verificationLog;
  extern llvm::cl::opt<std::string> masterSecretFile;
  extern llvm::cl::opt<bool> skipFree;
  extern llvm::cl::opt<bool> killFlags;
  extern llvm::cl::opt<bool> taseManager;
  extern llvm::cl::opt<bool> tasePreProcess;
  extern llvm::cl::opt<int> taseDebugArg;
  extern llvm::cl::opt<int> sleepDbgUsArg;
  //  extern llvm::cl::opt<bool> modelDebugArg;
  extern llvm::cl::opt<int> taseLocalStack;
  extern llvm::cl::opt<bool> taseFloatDebug;
  extern llvm::cl::opt<std::string> logFileArg;
  extern llvm::cl::opt<bool>  TASEIVC;
  extern llvm::cl::opt<bool>  cacheMLPredsArg;
  extern llvm::cl::opt<bool> TASEKillConsAfterVer;
  extern llvm::cl::opt<bool> dontFork;
  extern llvm::cl::opt<bool> workerSelfTerminate;
  extern llvm::cl::opt<bool> UseLegacyIndependentSolver;
  extern llvm::cl::opt<bool> UseCanonicalization;
  extern llvm::cl::opt<bool> enableBounceback;
  //extern llvm::cl::opt<bool> dropS2C;
  extern llvm::cl::opt<bool> measureTime;
  extern llvm::cl::opt<bool> useCMS4;
  extern llvm::cl::opt<bool> useXOROpt;
  extern llvm::cl::opt<std::string> project;
  extern llvm::cl::opt<std::string> clientName;
  extern llvm::cl::opt<std::string> mavlinkLog;
  extern llvm::cl::opt<int> mavlinkTraceNum;
  extern llvm::cl::opt<int> mavlinkMLMsgPadLen;
  extern llvm::cl::opt<bool> disableSpringboard;
  extern llvm::cl::opt<int> retryMax;
  extern llvm::cl::opt<int> QRMaxWorkers;
  extern llvm::cl::opt<int> tranMaxArgInp;
  extern llvm::cl::opt<bool> optimizeOvershiftChecks;
  extern llvm::cl::opt<bool> optimizeConstMemOps;

  extern llvm::cl::opt<bool> fixMHArg;
  extern llvm::cl::opt<bool> useMHWindowArg;
  extern llvm::cl::opt<bool> useMHWindowEdgesArg;
  extern llvm::cl::opt<bool> useMHWindowCoordsArg;
  extern llvm::cl::opt<int>  MHWindowSizeArg;
  extern llvm::cl::opt<int>  branchLimitForPriorityDecayArg;
  extern llvm::cl::opt<double> priorityDecayFactorArg;
  
  extern llvm::cl::opt<TASETrainType> trainType;
  extern llvm::cl::opt<bool> useConstraintBOW;
  extern llvm::cl::opt<bool> useBBBOW;
  extern llvm::cl::opt<VerTestType> verTestType;
  extern llvm::cl::opt<double> forkElisionPriorityThreshold;
  extern llvm::cl::opt<int>msgsToVerify;
  extern llvm::cl::opt<int> singleMsgVerificationIdxArg;
  extern llvm::cl::opt<int> tetrinetRandomSeed;
  extern llvm::cl::opt<int> tetrinetMaxRound;
  extern llvm::cl::opt<std::string> tetrinetLogArg;
  extern llvm::cl::opt<std::string> editDistanceOracleClustersArg;
  extern llvm::cl::opt<std::string> pathOracleFilePathArg;
  extern llvm::cl::opt<std::string> pathHistoryOracleFilePathArg;
  extern llvm::cl::opt<std::string> secondPathHistoryOracleFilePathArg;
  extern llvm::cl::opt<std::string> thirdPathHistoryOracleFilePathArg;
  extern llvm::cl::opt<std::string> jointOracleFilePathArg;
  extern llvm::cl::opt<std::string> secondJointOracleFilePathArg;
  extern llvm::cl::opt<std::string> thirdJointOracleFilePathArg;

  extern llvm::cl::opt<bool> useFallBackOracleArg;
  extern llvm::cl::opt<int>  fallBackBranchThresholdArg;
  extern llvm::cl::opt<bool>  multiOracleUseMessageHistoryOracleArg;
  extern llvm::cl::opt<bool> useAveragedOraclesArg;
  extern llvm::cl::opt<bool>  useCoordsWithoutMHArg;
  extern llvm::cl::opt<bool>  useBBForDenseArg;
  extern llvm::cl::opt<bool>  BBForDenseAndNoMHArg;
  extern llvm::cl::opt<bool>  BBForDenseAndLSTMMHArg;
  
  extern llvm::cl::opt<std::string> secondMHOracleFilePathArg;

  extern llvm::cl::opt<std::string> thirdMHOracleFilePathArg;
  
  extern llvm::cl::opt<std::string> mhOracleFilePathArg;
  extern llvm::cl::opt<bool>        useMLMH;
  extern llvm::cl::opt<bool>  printRecordsOnVerFail;
  extern llvm::cl::opt<bool> zeroMLMHArg;
  extern llvm::cl::opt<bool> useMsgFeatsInJointArg;
  extern llvm::cl::opt<bool> useFFOracleArg;
  extern llvm::cl::opt<bool>  pathAndMHOracleWithCoordsArg;
  extern llvm::cl::opt<int>  numberOfOraclesArg;
  
  extern llvm::cl::opt<int> msgsInPrevMsgWindowArg;
  extern llvm::cl::opt<bool> UseFastCexSolver;
  extern llvm::cl::opt<bool> updateSyntheticPaths;
  extern llvm::cl::opt<bool> makeInitialBranchMap;
  extern llvm::cl::opt<std::string> initialMessageBranchMapFile;
  extern llvm::cl::opt<std::string> updatedMessageBranchMapFile;
  extern llvm::cl::opt<std::string> updatedTetrilogFile;
  extern llvm::cl::opt<bool> printMHVecsAndExitArg;
  extern llvm::cl::opt<std::string> logIDStringArg;
  extern llvm::cl::opt<bool> UseCexCache;

extern llvm::cl::opt<bool> UseCache;

extern llvm::cl::opt<bool> UseIndependentSolver; 

extern llvm::cl::opt<bool> DebugValidateSolver;
  
extern llvm::cl::opt<int> MinQueryTimeToLog;

extern llvm::cl::opt<double> MaxCoreSolverTime;

extern llvm::cl::opt<bool> UseForkedCoreSolver;

extern llvm::cl::opt<bool> CoreSolverOptimizeDivides;

extern llvm::cl::opt<bool> UseAssignmentValidatingSolver;

  
///The different query logging solvers that can switched on/off
enum QueryLoggingSolverType
{
    ALL_KQUERY,   ///< Log all queries (un-optimised) in .kquery (KQuery) format
    ALL_SMTLIB,   ///< Log all queries (un-optimised)  .smt2 (SMT-LIBv2) format
    SOLVER_KQUERY,///< Log queries passed to solver (optimised) in .kquery (KQuery) format
    SOLVER_SMTLIB ///< Log queries passed to solver (optimised) in .smt2 (SMT-LIBv2) format
};

extern llvm::cl::bits<QueryLoggingSolverType> queryLoggingOptions;

enum CoreSolverType {
  STP_SOLVER,
  METASMT_SOLVER,
  DUMMY_SOLVER,
  Z3_SOLVER,
  NO_SOLVER
};
extern llvm::cl::opt<CoreSolverType> CoreSolverToUse;

extern llvm::cl::opt<CoreSolverType> DebugCrossCheckCoreSolverWith;

#ifdef ENABLE_METASMT

enum MetaSMTBackendType
{
    METASMT_BACKEND_STP,
    METASMT_BACKEND_Z3,
    METASMT_BACKEND_BOOLECTOR,
    METASMT_BACKEND_CVC4,
    METASMT_BACKEND_YICES2
};

extern llvm::cl::opt<klee::MetaSMTBackendType> MetaSMTBackend;

#endif /* ENABLE_METASMT */

class KCommandLine {
public:
  /// Hide all options except the ones in the specified category
  static void HideUnrelatedOptions(llvm::cl::OptionCategory &Category);

  /// Hide all options except the ones in the specified categories
  static void HideUnrelatedOptions(
      llvm::ArrayRef<const llvm::cl::OptionCategory *> Categories);
};
}

#endif	/* KLEE_COMMANDLINE_H */
