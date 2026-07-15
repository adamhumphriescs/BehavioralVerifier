/* -*- mode: c++; c-basic-offset: 2; -*- */

//===-- main.cpp ------------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Config/Version.h"
#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/TreeStream.h"
#include "klee/Internal/Support/Debug.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FileHandling.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/Support/PrintVersion.h"
#include "klee/Internal/System/Time.h"
#include "klee/Interpreter.h"
#include "klee/Statistics.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/Signals.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/system_error.h"
#endif

#include <dirent.h>
#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <cerrno>
#include <fstream>
#include <iomanip>
#include <iterator>
#include <sstream>

#include <stdlib.h>

//---------------------------------------------------------
//AH: BEGINNING OF TASE ADDITIONS (not including .h files)

#include <zlib.h>

#include "klee/CVAssignment.h"
#include "klee/util/ExprUtil.h"
//#include "tase/TASEControl.h"

#include <sys/prctl.h>
#include <sys/time.h>
#include <iostream>
#include <unordered_set>

#include <malloc.h>
#include <fcntl.h>

extern uint64_t saved_rax;



//gzFile log;
FILE* taseLog;

size_t MAX_RUNNING_WORKERS;
size_t MAX_STOPPED_WORKERS;

int trace_ID;
double target_start_time;
double target_end_time;
extern double run_start_time;
double last_message_verification_time;

#include "API_Scout.h"
#include "tase.h"
#include "tase_interp.h"
#include "API.h" //FIXME - Move declarations below into API.h
extern void manage_workers();
extern "C" void init_oracle();
extern "C" void setup_client();
extern void update_mh_singleMsgVerify(int i);
extern void setup_prev_mh_window(int currMsgNum, int windowSize);
extern void init_oracle_mh();
//extern void setupMLBBInfoMap();

extern void print_mavlink_msgs();


extern FILE * prev_stdout_log;

struct WorkerGroup *Stopped;
struct WorkerGroup *Running;
CVAssignment  prevMPA;
int round_count = 0;
int pass_count = 0;
#include "tase/EditDistanceOracle.h"
#include "../../lib/Tase/WorkerInfo.h"
#include "../../lib/Tase/WorkerGroup.h"
extern void testPQ(int PQTestSize);
extern void testBFS();
extern void testDFS();

//void loadMavlinkTrainingCluster(int msgIdx);
//extern int msgCtr;
extern void init_structures();
extern pid_t initial_fork();
extern int msgCtr;
extern void initSharedMLIDMem();;
extern std::vector<uint64_t> loadMavlinkTrainingCluster(); //Remove me

pid_t backup = 0;
pid_t scout = -1;

uint64_t trap_off;

extern target_ctx_t target_ctx;
tase_greg_t * target_ctx_gregs = target_ctx.gregs;
extern EXECUTION_STATE ex_state;
uint64_t rsp_global;
uint64_t targetMemAddr;
int glob_argc;
char ** glob_argv;
char ** glob_envp;
extern KTestObjectVector ktov;
extern "C" void begin_target_inner(int argc, char** argv);
extern "C" void klee_interp();

extern "C" bool large_buf_has_taint_16_128(const uint16_t*, const int);
extern "C" bool large_buf_has_taint_32_128(const uint16_t*, const int);
extern "C" bool large_buf_has_taint_16_256(const uint16_t*, const int);
extern "C" bool large_buf_has_taint_32_256(const uint16_t*, const int);

extern "C" bool (*large_buf_has_taint)(const uint16_t*, const int) = NULL;

std::unordered_set<uint64_t> cartridge_heads;
std::unordered_set<uint64_t> cartridge_entry_points;
std::unordered_set<uint64_t> kill_flags;
std::unordered_map<uint64_t, std::pair<uint32_t, uint32_t>> cartridge_regstatus;

#ifdef TASE_OPENSSL
extern "C" void s_client_main(int argc, char ** argv);
#endif

//This struct is to help the solver for basic blocks with only
//two possible successors (e.g., blocks ending in "jb", "je", etc).

typedef struct cartridgeDestHint {
  uint64_t blockTop;
  uint64_t dest1;
  uint64_t dest2;
} cartridgeSuccessorInfo;

std::map<uint64_t, cartridgeSuccessorInfo> knownCartridgeDests;
std::stringstream worker_ID_stream;
std::string prev_worker_ID;
klee::Interpreter * GlobalInterpreter;
llvm::Module * interpModule;

extern char * ktestModePtr;
extern char * ktestPathPtr;
extern char ktestMode[20];
extern char ktestPath[100];
extern int * target_started_ptr;
extern std::map<uint64_t, KFunction *> IR_KF_Map;

//extern "C" void cycleTASELogs(bool isReplay);


int masterPID;
bool enableMultipass = false;;
int taseDebug;
int sleepDbgUs;
int localStack;
bool singleStepping;
bool noLog;
std::string logFile;
bool dropS2C;
bool enableTimeSeries;
bool bufferGuard;
int orig_stdout_fd;

extern "C" {
  std::string oracleFilePath;
}
std::string jointOracleFilePath;
std::string pathHistoryOracleFilePath;
std::string messageHistoryOracleFilePath;

std::string secondJointOracleFilePath;
std::string secondPathHistoryOracleFilePath;
std::string secondMHOracleFilePath;

std::string thirdJointOracleFilePath;
std::string thirdPathHistoryOracleFilePath;
std::string thirdMHOracleFilePath;


namespace klee {
  std::string clientNameExternal; // For external apps that don't like cl::opt
  bool cacheMLPreds;
  std::string editDistanceOracleClusters;
  int singleMsgVerificationIdx;
  std::string tetrinetLog;
  bool zeroMLMH;
  int msgsInPrevMsgWindow;
  bool fixMH;
  bool useMsgFeatsInJoint;
  bool useMHWindow;
  int MHWindowSize;
  bool useMHWindowEdges;
  bool useMHWindowCoords;
  int branchLimitForPriorityDecay;
  double priorityDecayFactor;
  bool useFFOracle;
  int numberOfOracles;
  bool pathAndMHOracleWithCoords;
  bool useLEARCHFeatsOracle;
  bool useFallBackOracle;//Determine if we need to fall back to another oracle after a certain threshold is reached
  int fallBackBranchThreshold;//Fall back to the second oracle if we fail to verify in branches less than or equal to this number
  bool fallbackOracleActive = false; // Whether we should be using the main or fallback oracle.  Should flip back to false after each verification round.
  bool multiOracleUseMessageHistoryOracle;//Indicates if multiple oracles need unique MH oracle
  bool useAveragedOracles;
  bool useCoordsWithoutMH;
  bool useBBForDense;
  bool BBForDenseAndNoMH;
  bool BBForDenseAndLSTMMH;
};

#ifdef TASE_BIGNUM
extern int symIndex;
extern int numEntries;
#endif
//extern void  exit_tase();
extern uint64_t cartridge_rip;

//extern void setup_ml_oracle(const char * oracleFilePath);
//extern double warm_up_ml_oracle();
extern char tase_progname[];

uint64_t tranMaxArg;

std::string vtt_to_string(VerTestType t) {
  switch(t) {
  case VerTestType::EXPLORATION:
    return "EXPLORATION";
    break;
  case VerTestType::TRAIN:
    return "TRAIN";
    break;
  case VerTestType::REPLAY:
    return "REPLAY";
    break;
  case VerTestType::VERIFY:
    return "VERIFY";
    break;
  case VerTestType::SINGLEMSGVER:
    return "SINGLEMSGVER";
    break;
  }
}

extern void calcMHVecsAndExit();

//AH: END OF TASE ADDITIONS
//-----------------------------------

using namespace llvm;
using namespace klee;

namespace klee {
      
  cl::opt<runType>
  execMode("execMode", cl::desc("INTERP_ONLY or MIXED (native and interpretation)"),
	      cl::values(clEnumValN(INTERP_ONLY, "INTERP_ONLY", "only execute via interpreter"),
                  clEnumValN(MIXED, "MIXED", "execute natively in transactions and interpret ")
		  KLEE_LLVM_CL_VAL_END),

	      cl::init(MIXED));


  // cl::opt<TASETestType>
  // testType("testType", cl::desc("EXPLORATION or VERIFICATION"),
  // 	      cl::values(clEnumValN(EXPLORATION, "EXPLORATION", "Just execute and don't try to verify or do multiple passes"),
  //                 clEnumValN(VERIFICATION, "VERIFICATION", "Mark certain functions as symbolic and attempt to verify against a message log with multipass ")
  // 									     KLEE_LLVM_CL_VAL_END),	      
  // 	      cl::init(EXPLORATION));

  cl::opt<VerTestType> verTestType("verTestType", cl::desc("Either replay, verification, singleMsgVerification, or train"),
				   cl::values(clEnumValN(VerTestType::EXPLORATION, "exploration", "exploration"),
					      clEnumValN(VerTestType::TRAIN, "train", "training"),
					      clEnumValN(VerTestType::REPLAY, "replay", "replay"),
					      clEnumValN(VerTestType::VERIFY, "verification", "verification"),
					      clEnumValN(VerTestType::SINGLEMSGVER, "singleMsgVerify", "singleMsgVerify")
					      KLEE_LLVM_CL_VAL_END),				   
				   cl::init(VerTestType::EXPLORATION));


  cl::opt<double> forkElisionPriorityThreshold ("forkElisionPriorityThreshold", cl::desc("Branches with priority below this will have to be explored with a replay later"), cl::init(-1.0));
  
  cl::opt<int>
  trapOffset("trapOffset", cl::desc("Trap offset for TASE, default 12, 33 for static taint"), cl::init(12));
  
  
  cl::opt<TASEExplorationType>
  explorationType("explorationType", cl::desc("BFS, DFS, ML (Path Oracle) , or ED (Edit Distance)"),
		  cl::values(clEnumValN(TASEExplorationType::DFS, "DFS", "Depth-first search"),
			     clEnumValN(TASEExplorationType::BFS, "BFS", "Breadth-first search" ),
			     clEnumValN(TASEExplorationType::ML, "ML", "ML-based Path Oracle" ),
			     clEnumValN(TASEExplorationType::ED, "ED", "Edit Distance Oracle" )
			     KLEE_LLVM_CL_VAL_END),

		  cl::init(TASEExplorationType::BFS));

  cl::opt<PoisonSize>
  poisonSize("poisonSize", cl::desc("WORD or DWORD"),
	      cl::values(clEnumValN(WORD, "WORD", "2 bytes"),
			 clEnumValN(DWORD, "DWORD", "4 bytes")
			 KLEE_LLVM_CL_VAL_END),
	      cl::init(WORD));

  cl::opt<SIMDType>
  simdType("SIMDType", cl::desc("XMM or YMM"),
	   cl::values(clEnumValN(XMM, "XMM", "XMM Registers, 128-bit"),
		      clEnumValN(YMM, "YMM", "YMM Registers, 256-bit")
		      //clEnumValN(ZMM, "ZMM", "ZMM Registers, 512-bit")
		      KLEE_LLVM_CL_VAL_END),
	   cl::init(XMM));

  cl::opt<int> maxRunning("maxRunning", cl::desc("max running workers"), cl::init(1));
  cl::opt<int> maxStopped("maxStopped", cl::desc("max stopped workers"), cl::init(1024));  
  
  cl::opt<std::string> verificationLog("verificationLog", cl::desc("ktest file to verify against for OpenSSL "), cl::init("./ssl.ktest"));

  cl::opt<std::string> masterSecretFile("masterSecretFile", cl::desc("File containing master secret for OpenSSL verification"), cl::init("./ssl.mastersecret"));
  
  cl::opt<bool>
  skipFree("skipFree", cl::desc("Debugging option to skip frees"), cl::init(false));

  cl::opt<bool>
  TASEIVC("TASEIVC", cl::desc("Debugging option to concretize regs if possible"), cl::init(false));

  cl::opt<bool>
  TASEKillConsAfterVer("TASEKillConsAfterVer", cl::desc("Debugging option to remove constraints after verification round"), cl::init(false));
  
  cl::opt<bool>
  bufferGuardArg("bufferGuard", cl::desc("Add poison zones around heap buffers"), cl::init(false));
  
  cl::opt<bool>
  killFlags("killFlags", cl::desc("Option to kill dead flags register after each jump to the springboard"), cl::init(true));  
  
  cl::opt<bool>
  taseManager("taseManager", cl::desc("Fork off a manager process in TASE.  Expect a fork bomb if false."), cl::init(true));

  cl::opt<bool>
  tasePreProcess("tasePreProcess", cl::desc("Set to TRUE to run preprocessing in TASE and generate IR with code located in the executable"), cl::init(false));
  cl::opt<int>
  sleepDbgUsArg("sleepDbgUs", cl::desc("Number of microseconds to sleep between verification rounds"), cl::init(0)); 
  
  cl::opt<int>
  taseDebugArg("taseDebug", cl::desc("Verbose logging in TASE"), cl::init(0));
  
  cl::opt<int>
  taseLocalStack("localStack", cl::desc("size of local stack range to print"), cl::init(0));

  cl::opt<bool>
  singleSteppingArg("singleStepping", cl::desc("bitcode is single-instruction functions"), cl::init(false));
  
  //  cl::opt<bool>
  //  modelDebugArg("modelDebug", cl::desc("Logging for models in TASE"), cl::init(false));

  cl::opt<bool>
  taseFloatDebug("taseFloatDebug", cl::desc("Log results of soft float emulation routines"), cl::init(true));
  
  cl::opt<bool>
  dontFork("dontFork", cl::desc("Disable forking in TASE for debugging"), cl::init(false));

  cl::opt<std::string>
  logFileArg("log", cl::desc("Filename or \"false\" for no logging in TASE"), cl::init("Monitor"));
  
  cl::opt<bool>
  workerSelfTerminate("workerSelfTerminate", cl::desc("Workers will exit if they see they're in an earlier round"), cl::init(true));

  cl::opt<bool>
  UseLegacyIndependentSolver("use-legacy-independent-solver", cl::desc("Per cliver, pass through getInitialValue call in the independent solver without aggressive optimization"), cl::init(true));

  cl::opt<bool>
  UseCanonicalization("UseCanonicalization", cl::desc("Per cliver, canonicalize queries to be independent of variable name"), cl::init(true));
  
  cl::opt<bool>
  enableBounceback("enableBounceback", cl::desc("Try to bounce back to native execution in TASE depending on abort code"), cl::init(true));

  cl::opt<bool>
  dropS2CArg("dropS2C", cl::desc("Drop server to client messages for verification after the handshake"), cl::init(false));

  cl::opt<bool>
  enableTimeSeriesArg("enableTimeSeries", cl::desc("Perform verification across 21 traces and wait between message arrivals to simulate actual test conditions"), cl::init(false));
  
  cl::opt<bool>
  measureTime("measureTime", cl::desc("Time interpretation rounds in TASE for debugging"), cl::init(false));

  cl::opt<bool>
  useCMS4("useCMS4", cl::desc("Use cryptominisat4 instead of minisat as the SAT backend for STP "), cl::init(true));

  cl::opt<bool>
  useXOROpt("useXOROpt", cl::desc("Use optimization from cliver to eliminate unnecessary XOR expressions when using solver in writesocket model"), cl::init(true));
  
  cl::opt<std::string>
  project("project", cl::desc("Name of project in TASE"), cl::init("-"));

  cl::opt<std::string>
  clientName("clientName", cl::desc("Name of client verified in TASE, such as TETRINET or MAVLINK"), cl::init(""));

  cl::opt<int>
  mavlinkMLMsgPadLen("mavlinkMLMsgPadLen", cl::desc("Length to pad messages when extracting mavlink features.  Should be len of longest message"), cl::init(-1));
  
  cl::opt<std::string>
  mavlinkLog("mavlinkLog", cl::desc("File path of mavlink log "), cl::init("UNDEFINED"));

  cl::opt<int>
  mavlinkTraceNum("mavlinkTraceNum", cl::desc("Number of mavlink trace.  Each logged run of a drone constitutes a trace."), cl::init(-1));
  
  cl::opt<bool>
  disableSpringboard("disableSpringboard", cl::desc("Enable or noop the springboard"), cl::init(false));

  cl::opt<int>
  retryMax("retryMax", cl::desc("Number of times to try and bounceback to native execution if abort status allows it "), cl::init(1));

  cl::opt<int>
  QRMaxWorkers("QRMaxWorkers", cl::desc("Maximum number of workers in TASE "), cl::init(8));
  
  cl::opt<int>
  tranMaxArgInp("tranBBMax", cl::desc("Max number of basic blocks to wrap into a single transaction"), cl::init(16));

  cl::opt<TASETrainType>
  trainType("trainType", cl::desc("Type of training.  Should either be ML or CLUSTER"),
	    cl::values(clEnumValN(TASETrainType::ML, "ML", "Train for an ml based oracle"),
		       clEnumValN(TASETrainType::CLUSTER, "CLUSTER", "Train for a cluster based oracle")
		       KLEE_LLVM_CL_VAL_END),
	    cl::init(TASETrainType::CLUSTER));
  
  cl::opt<bool>
  useBBBOW("useBBBOW", cl::desc("Add BOW representation of basic block IDs for training purposes"), cl::init(false));
  
  cl::opt<bool>
  useConstraintBOW("useConstraintBOW", cl::desc("Add constraint BOW representation for training purposes"), cl::init(false));

  cl::opt<bool>
  cacheMLPredsArg("cacheMLPreds", cl::desc("Cache ML Preds to reduce inference times"), cl::init(true));
  
  cl::opt<int>msgsToVerify("msgsToVerify", cl::desc("Number of messages in log to verify"), cl::init(-1));
  
  cl::opt<int>
  singleMsgVerificationIdxArg("singleMsgVerificationIdx", cl::desc("Index of single msg to verify."), cl::init(-1));

  cl::opt<bool>
  makeInitialBranchMap("makeInitialBranchMap", cl::desc("Make a map containing branches per message"), cl::init(false));

  cl::opt<bool>
  updateSyntheticPaths("updateSyntheticPaths", cl::desc("Update our best paths seen so far when a synthetic path is better that the previous best.For synth training."), cl::init(false));

  cl::opt<std::string>
  initialMessageBranchMapFile("initialMessageBranchMapFile", cl::desc("initial list of lowest number of branches per message. For synth training."), cl::init("NONE"));

  cl::opt<std::string>
  updatedMessageBranchMapFile("updatedMessageBranchMapFile", cl::desc("filename of updated lowest number of branches per message after training with LSTM.For synth training."), cl::init("NONE"));

  cl::opt<std::string>
  updatedTetrilogFile("updatedTetrilogFile", cl::desc("File with updated version of tetrilog after shorter path is found and new keystrokes replace the older version. For synth training"), cl::init("NONE"));

  cl::opt<bool>
  fixMHArg("fixMH", cl::desc("Force message history to be a fixed vector in fixedMH.txt"), cl::init(false));

  cl::opt<int>
  branchLimitForPriorityDecayArg("branchLimitForPriorityDecay", cl::desc("If a candidate branch has already required more than X symbolic branches, discount its priority"), cl::init(230));

  cl::opt<double>
  priorityDecayFactorArg("priorityDecayFactor", cl::desc("This is a constant between 0 and 1 which is multiplied by itself to discount priorities for long paths.  1 disables"), cl::init(1.0));
  
  cl::opt<bool>
  useMHWindowArg("useMHWindow", cl::desc("Force message history to be a Window "), cl::init(false));

  cl::opt<bool>
  useMHWindowEdgesArg("useMHWindowEdges", cl::desc("Force message history to be a Window with the edges around previous pieces "), cl::init(false));

  cl::opt<bool>
  useMHWindowCoordsArg("useMHWindowCoords", cl::desc("Force message history to be a Window with the coordinates of previous pieces "), cl::init(false));

  cl::opt<bool>
  useFFOracleArg("useFFOracle", cl::desc("Use an oracle which just a feedforward NN "), cl::init(false));

  cl::opt<bool>
  useFallBackOracleArg("useFallBackOracle", cl::desc("Fall back to a backup oracle if primary oracle fails to verify in fallBackBranchThreshold branches"), cl::init(false));

  cl::opt<bool>
  multiOracleUseMessageHistoryOracleArg("multiOracleUseMessageHistoryOracle", cl::desc("If we're using multiple oracles, whether or not they need to use a distinct message history oracle"), cl::init(false));

  cl::opt<bool>
  useCoordsWithoutMHArg("useCoordsWithoutMH", cl::desc("Use an oracle that uses message coords but not history.  For TetriNET"), cl::init(false));

  cl::opt<bool>
  useBBForDenseArg("useBBForDense", cl::desc("Feed extra BB-specific feats into the dense layers"), cl::init(false));

  cl::opt<bool>
  BBForDenseAndNoMHArg("BBForDenseAndNoMH", cl::desc("Feed extra BB-specific feats into the dense layers. No message history"), cl::init(false));
  
  cl::opt<bool>
  BBForDenseAndLSTMMHArg("BBForDenseAndLSTMMH", cl::desc("Feed extra BB-specific feats into the dense layers. Message history from LSTM"), cl::init(false));
  
  cl::opt<bool>
  useAveragedOraclesArg("useAveragedOracles", cl::desc("If we're using multiple oracles, invoke all of them and use the average for the priority"), cl::init(false));
  
  cl::opt<int>
  fallBackBranchThresholdArg("fallBackBranchThreshold", cl::desc("If primary oracle fails to verify in this number of branches, swap to fallback oracle"), cl::init(2000));
  
  cl::opt<bool>
  pathAndMHOracleWithCoordsArg("pathAndMHOracleWithCoords", cl::desc("Use an oracle with PH and MH and coords in the MH "), cl::init(false));

  cl::opt<bool>
  useLEARCHFeatsOracleArg("useLEARCHFeatsOracle", cl::desc("Use an oracle which uses the LEARCH constraint BOW feats "), cl::init(false));
  
  cl::opt<int>
  MHWindowSizeArg("MHWindowSize", cl::desc("Window size for message history"), cl::init(-1));

  cl::opt<int>
  numberOfOraclesArg("numberOfOracles", cl::desc("Number of oracles to use"), cl::init(1));
  
  cl::opt<int>
  tetrinetMaxRound("tetrinetMaxRound", cl::desc("Max number of blocks to drop in tetrinet"), cl::init(300));
  
  cl::opt<int>
  tetrinetRandomSeed("tetrinetRandomSeed", cl::desc("Force seed value in tetrinet from command line"), cl::init(-1));
  
  cl::opt<std::string> tetrinetLogArg("tetrinetLog", cl::desc("Log with messages for TASE to verify"));
  
  cl::opt<std::string> editDistanceOracleClustersArg("editDistanceOracleClusters", cl::desc("File with cluster information needed to implement an edit distance oracle"));
  
  cl::opt<bool>
  optimizeOvershiftChecks("optimizeOvershiftChecks", cl::desc("Incorporate KLEE 2.1 optimization to simplify overshift checks"), cl::init(true));

  cl::opt<bool>
  optimizeConstMemOps("optimizeConstMemOps", cl::desc("Use optimizations for load/stores at constant offsets"), cl::init(false));

  cl::opt<std::string>
  mhOracleFilePathArg("mhOracleFilePath", cl::desc("Location of trained message history model for path selection in TASE"));
  
  cl::opt<std::string>
  jointOracleFilePathArg("jointOracleFilePath", cl::desc("Location of trained joint model for path selection in TASE"));

  cl::opt<std::string>
  secondMHOracleFilePathArg("secondMHOracleFilePath", cl::desc("Second MH Oracle file path"));

  cl::opt<std::string>
  thirdMHOracleFilePathArg("thirdMHOracleFilePath", cl::desc("Second MH Oracle file path"));
  
  cl::opt<std::string>
  secondJointOracleFilePathArg("secondJointOracleFilePath", cl::desc("Location of trained joint model for path selection in TASE"));

  cl::opt<std::string>
  thirdJointOracleFilePathArg("thirdJointOracleFilePath", cl::desc("Location of trained joint model for path selection in TASE"));
  
  cl::opt<std::string>
  pathHistoryOracleFilePathArg("pathHistoryOracleFilePath", cl::desc("Location of trained model for path selection in TASE")); 

  cl::opt<std::string>
  secondPathHistoryOracleFilePathArg("secondPathHistoryOracleFilePath", cl::desc("Location of trained model for path selection in TASE"));

  cl::opt<std::string>
  thirdPathHistoryOracleFilePathArg("thirdPathHistoryOracleFilePath", cl::desc("Location of trained model for path selection in TASE"));
  
  cl::opt<std::string>
  pathOracleFilePath("pathOracleFilePath", cl::desc("Location of trained model for path selection in TASE"), cl::init("/winhomes/abh61/merge01192024/TASE_Private/cppflow/model_LSTM_2Layer_BBBOW_Mavlink3"));

  cl::opt<bool>
  printRecordsOnVerFail("printRecordsOnVerFail", cl::desc("Even if full verification fails, attempt to print records about the messages verified so far \n"), cl::init(false));
  
  cl::opt<bool>
  useMLMH("useMLMH", cl::desc("Use message history with ML oracle.  Requires extra oracles \n"), cl::init(false));

  cl::opt<bool>
  zeroMLMHArg("zeroMLMH", cl::desc("Force ML MH vector to be all zeros for debugging \n"), cl::init(false));

  cl::opt<int>
  msgsInPrevMsgWindowArg("msgsInPrevMsgWindow", cl::desc("Force message history to encompass previous X msgs.  Defaults to -1, which represents all prev msgs"), cl::init(-1));
  
  cl::opt<bool>
  useMsgFeatsInJointArg("useMsgFeatsInJoint", cl::desc("Explicitly add msg feats in joint oracle.  Currently only works for tetrinet"), cl::init(false));
  
  cl::opt<bool>
  printMHVecsAndExitArg("printMHVecsAndExit", cl::desc("Print Message history vectors and other features.  Don't actually do any verification"), cl::init(false));

  cl::opt<std::string>
  logIDStringArg("logIDString", cl::desc("String to append to LOG_RECORD results at end of eval. Just a convenience."), cl::init(""));
}

namespace {
  cl::opt<std::string>
  InputFile(cl::desc("<input bytecode>"), cl::Positional, cl::init("-"));

  
  cl::opt<std::string>
  EntryPoint("entry-point",
               cl::desc("Consider the function with the given name as the entrypoint"),
               cl::init("_Z9dummyMainv"));

  cl::opt<std::string>
  RunInDir("run-in", cl::desc("Change to the given directory prior to executing"));

  cl::opt<std::string>
  Environ("environ", cl::desc("Parse environ from given file (in \"env\" format)"));

  cl::list<std::string>
  InputArgv(cl::ConsumeAfter,
            cl::desc("<program arguments>..."));

  cl::opt<bool>
  NoOutput("no-output",
           cl::desc("Don't generate test files"));

  cl::opt<bool>
  WarnAllExternals("warn-all-externals",
                   cl::desc("Give initial warning for all externals."));

  cl::opt<bool>
  WriteCVCs("write-cvcs",
            cl::desc("Write .cvc files for each test case"));

  cl::opt<bool>
  WriteKQueries("write-kqueries",
            cl::desc("Write .kquery files for each test case"));

  cl::opt<bool>
  WriteSMT2s("write-smt2s",
            cl::desc("Write .smt2 (SMT-LIBv2) files for each test case"));

  cl::opt<bool>
  WriteCov("write-cov",
           cl::desc("Write coverage information for each test case"));

  cl::opt<bool>
  WriteTestInfo("write-test-info",
                cl::desc("Write additional test case information"));

  cl::opt<bool>
  WritePaths("write-paths",
                cl::desc("Write .path files for each test case"));

  cl::opt<bool>
  WriteSymPaths("write-sym-paths",
                cl::desc("Write .sym.path files for each test case"));

  cl::opt<bool>
  OptExitOnError("exit-on-error",
              cl::desc("Exit if errors occur"));

  enum LibcType {
    NoLibc, KleeLibc, UcLibc
  };

  cl::opt<LibcType>
  Libc("libc",
       cl::desc("Choose libc version (none by default)."),
       cl::values(clEnumValN(NoLibc, "none", "Don't link in a libc"),
                  clEnumValN(KleeLibc, "klee", "Link in klee libc"),
		  clEnumValN(UcLibc, "uclibc", "Link in uclibc (adapted for klee)")
		  KLEE_LLVM_CL_VAL_END),
       cl::init(NoLibc));


  cl::opt<bool>
  WithPOSIXRuntime("posix-runtime",
		cl::desc("Link with POSIX runtime.  Options that can be passed as arguments to the programs are: --sym-arg <max-len>  --sym-args <min-argvs> <max-argvs> <max-len> + file model options"),
		cl::init(false));

  cl::opt<bool>
  OptimizeModule("optimize",
                 cl::desc("Optimize before execution"),
		 cl::init(false));

  cl::opt<bool>
  CheckDivZero("check-div-zero",
               cl::desc("Inject checks for division-by-zero"),
               cl::init(true));

  cl::opt<bool>
  CheckOvershift("check-overshift",
               cl::desc("Inject checks for overshift"),
               cl::init(true));

  cl::opt<std::string>
  OutputDir("output-dir",
            cl::desc("Directory to write results in (defaults to klee-out-N)"),
            cl::init(""));

  cl::opt<bool>
  ReplayKeepSymbolic("replay-keep-symbolic",
                     cl::desc("Replay the test cases only by asserting "
                              "the bytes, not necessarily making them concrete."));

  cl::list<std::string>
      ReplayKTestFile("replay-ktest-file",
                      cl::desc("Specify a ktest file to use for replay"),
                      cl::value_desc("ktest file"));

  cl::list<std::string>
      ReplayKTestDir("replay-ktest-dir",
                   cl::desc("Specify a directory to replay ktest files from"),
                   cl::value_desc("output directory"));

  cl::opt<std::string>
  ReplayPathFile("replay-path",
                 cl::desc("Specify a path file to replay"),
                 cl::value_desc("path file"));

  cl::list<std::string>
  SeedOutFile("seed-out");

  cl::list<std::string>
  SeedOutDir("seed-out-dir");

  cl::list<std::string>
  LinkLibraries("link-llvm-lib",
		cl::desc("Link the given libraries before execution"),
		cl::value_desc("library file"));

  cl::opt<unsigned>
  MakeConcreteSymbolic("make-concrete-symbolic",
                       cl::desc("Probabilistic rate at which to make concrete reads symbolic, "
				"i.e. approximately 1 in n concrete reads will be made symbolic (0=off, 1=all).  "
				"Used for testing."),
                       cl::init(0));

  cl::opt<unsigned>
  StopAfterNTests("stop-after-n-tests",
	     cl::desc("Stop execution after generating the given number of tests.  Extra tests corresponding to partially explored paths will also be dumped."),
	     cl::init(0));

  cl::opt<bool>
  Watchdog("watchdog",
           cl::desc("Use a watchdog process to enforce --max-time."),
           cl::init(0));
}

extern cl::opt<double> MaxTime;

/***/

class KleeHandler : public InterpreterHandler {
private:
  Interpreter *m_interpreter;
  TreeStreamWriter *m_pathWriter, *m_symPathWriter;
  llvm::raw_ostream *m_infoFile;

  SmallString<128> m_outputDirectory;

  unsigned m_numTotalTests;     // Number of tests received from the interpreter
  unsigned m_numGeneratedTests; // Number of tests successfully generated
  unsigned m_pathsExplored; // number of paths explored so far

  // used for writing .ktest files
  int m_argc;
  char **m_argv;

public:
  KleeHandler(int argc, char **argv);
  ~KleeHandler();

  llvm::raw_ostream &getInfoStream() const { return *m_infoFile; }
  /// Returns the number of test cases successfully generated so far
  unsigned getNumTestCases() { return m_numGeneratedTests; }
  unsigned getNumPathsExplored() { return m_pathsExplored; }
  void incPathsExplored() { m_pathsExplored++; }

  void setInterpreter(Interpreter *i);

  void processTestCase(const ExecutionState  &state,
                       const char *errorMessage,
                       const char *errorSuffix);

  std::string getOutputFilename(const std::string &filename);
  llvm::raw_fd_ostream *openOutputFile(const std::string &filename);
  std::string getTestFilename(const std::string &suffix, unsigned id);
  llvm::raw_fd_ostream *openTestFile(const std::string &suffix, unsigned id);

  // load a .path file
  static void loadPathFile(std::string name,
                           std::vector<bool> &buffer);

  static void getKTestFilesInDir(std::string directoryPath,
                                 std::vector<std::string> &results);

  static std::string getRunTimeLibraryPath(const char *argv0);
};

KleeHandler::KleeHandler(int argc, char **argv)
    : m_interpreter(0), m_pathWriter(0), m_symPathWriter(0), m_infoFile(0),
      m_outputDirectory(), m_numTotalTests(0), m_numGeneratedTests(0),
      m_pathsExplored(0), m_argc(argc), m_argv(argv) {

  // create output directory (OutputDir or "klee-out-<i>")
  bool dir_given = OutputDir != "";
  SmallString<128> directory(dir_given ? OutputDir : InputFile);

  if (!dir_given) sys::path::remove_filename(directory);
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
  if ((ec = sys::fs::make_absolute(directory)) != errc::success) {
#else
  if (auto ec = sys::fs::make_absolute(directory)) {
#endif
    klee_error("unable to determine absolute path: %s", ec.message().c_str());
  }

  if (dir_given) {
    // OutputDir
    if (mkdir(directory.c_str(), 0775) < 0)
      klee_error("cannot create \"%s\": %s", directory.c_str(), strerror(errno));

    m_outputDirectory = directory;
  } else {
    // "klee-out-<i>"
    int i = 0;
    for (; i <= INT_MAX; ++i) {
      SmallString<128> d(directory);
      llvm::sys::path::append(d, "klee-out-");
      raw_svector_ostream ds(d); ds << i; ds.flush();

      // create directory and try to link klee-last
      if (mkdir(d.c_str(), 0775) == 0) {
        m_outputDirectory = d;

        SmallString<128> klee_last(directory);
        llvm::sys::path::append(klee_last, "klee-last");

        if (((unlink(klee_last.c_str()) < 0) && (errno != ENOENT)) ||
            symlink(m_outputDirectory.c_str(), klee_last.c_str()) < 0) {

          klee_warning("cannot create klee-last symlink: %s", strerror(errno));
        }

        break;
      }

      // otherwise try again or exit on error
      if (errno != EEXIST)
        klee_error("cannot create \"%s\": %s", m_outputDirectory.c_str(), strerror(errno));
    }
    if (i == INT_MAX && m_outputDirectory.str().equals(""))
        klee_error("cannot create output directory: index out of range");
  }

  klee_message("output directory is \"%s\"", m_outputDirectory.c_str());

  // open warnings.txt
  std::string file_path = getOutputFilename("warnings.txt");
  if ((klee_warning_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

  // open messages.txt
  file_path = getOutputFilename("messages.txt");
  if ((klee_message_file = fopen(file_path.c_str(), "w")) == NULL)
    klee_error("cannot open file \"%s\": %s", file_path.c_str(), strerror(errno));

  // open info
  m_infoFile = openOutputFile("info");
}

KleeHandler::~KleeHandler() {
  delete m_pathWriter;
  delete m_symPathWriter;
  fclose(klee_warning_file);
  fclose(klee_message_file);
  delete m_infoFile;
}

void KleeHandler::setInterpreter(Interpreter *i) {
  m_interpreter = i;

  if (WritePaths) {
    m_pathWriter = new TreeStreamWriter(getOutputFilename("paths.ts"));
    assert(m_pathWriter->good());
    m_interpreter->setPathWriter(m_pathWriter);
  }

  if (WriteSymPaths) {
    m_symPathWriter = new TreeStreamWriter(getOutputFilename("symPaths.ts"));
    assert(m_symPathWriter->good());
    m_interpreter->setSymbolicPathWriter(m_symPathWriter);
  }
}

std::string KleeHandler::getOutputFilename(const std::string &filename) {
  SmallString<128> path = m_outputDirectory;
  sys::path::append(path,filename);
  return path.str();
}

llvm::raw_fd_ostream *KleeHandler::openOutputFile(const std::string &filename) {
  llvm::raw_fd_ostream *f;
  std::string Error;
  std::string path = getOutputFilename(filename);
  f = klee_open_output_file(path, Error);
  if (!Error.empty()) {
    klee_warning("error opening file \"%s\".  KLEE may have run out of file "
                 "descriptors: try to increase the maximum number of open file "
                 "descriptors by using ulimit (%s).",
                 path.c_str(), Error.c_str());
    return NULL;
  }
  return f;
}

std::string KleeHandler::getTestFilename(const std::string &suffix, unsigned id) {
  std::stringstream filename;
  filename << "test" << std::setfill('0') << std::setw(6) << id << '.' << suffix;
  return filename.str();
}

llvm::raw_fd_ostream *KleeHandler::openTestFile(const std::string &suffix,
                                                unsigned id) {
  return openOutputFile(getTestFilename(suffix, id));
}


/* Outputs all files (.ktest, .kquery, .cov etc.) describing a test case */
void KleeHandler::processTestCase(const ExecutionState &state,
                                  const char *errorMessage,
                                  const char *errorSuffix) {
  if (errorMessage && OptExitOnError) {
    m_interpreter->prepareForEarlyExit();
    klee_error("EXITING ON ERROR:\n%s\n", errorMessage);
  }

  if (!NoOutput) {
    std::vector< std::pair<std::string, std::vector<unsigned char> > > out;
    bool success = m_interpreter->getSymbolicSolution(state, out);

    if (!success)
      klee_warning("unable to get symbolic solution, losing test case");

    double start_time = util::getWallTime();

    unsigned id = ++m_numTotalTests;

    if (success) {
      KTest b;
      b.numArgs = m_argc;
      b.args = m_argv;
      b.symArgvs = 0;
      b.symArgvLen = 0;
      b.numObjects = out.size();
      b.objects = new KTestObject[b.numObjects];
      assert(b.objects);
      for (unsigned i=0; i<b.numObjects; i++) {
        KTestObject *o = &b.objects[i];
        o->name = const_cast<char*>(out[i].first.c_str());
        o->numBytes = out[i].second.size();
        o->bytes = new unsigned char[o->numBytes];
        assert(o->bytes);
        std::copy(out[i].second.begin(), out[i].second.end(), o->bytes);
      }

      if (!kTest_toFile(&b, getOutputFilename(getTestFilename("ktest", id)).c_str())) {
        klee_warning("unable to write output test case, losing it");
      } else {
        ++m_numGeneratedTests;
      }

      for (unsigned i=0; i<b.numObjects; i++)
        delete[] b.objects[i].bytes;
      delete[] b.objects;
    }

    if (errorMessage) {
      llvm::raw_ostream *f = openTestFile(errorSuffix, id);
      *f << errorMessage;
      delete f;
    }

    if (m_pathWriter) {
      std::vector<unsigned char> concreteBranches;
      m_pathWriter->readStream(m_interpreter->getPathStreamID(state),
                               concreteBranches);
      llvm::raw_fd_ostream *f = openTestFile("path", id);
      for (std::vector<unsigned char>::iterator I = concreteBranches.begin(),
                                                E = concreteBranches.end();
           I != E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (errorMessage || WriteKQueries) {
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints,Interpreter::KQUERY);
      llvm::raw_ostream *f = openTestFile("kquery", id);
      *f << constraints;
      delete f;
    }

    if (WriteCVCs) {
      // FIXME: If using Z3 as the core solver the emitted file is actually
      // SMT-LIBv2 not CVC which is a bit confusing
      std::string constraints;
      m_interpreter->getConstraintLog(state, constraints, Interpreter::STP);
      llvm::raw_ostream *f = openTestFile("cvc", id);
      *f << constraints;
      delete f;
    }

    if(WriteSMT2s) {
      std::string constraints;
        m_interpreter->getConstraintLog(state, constraints, Interpreter::SMTLIB2);
        llvm::raw_ostream *f = openTestFile("smt2", id);
        *f << constraints;
        delete f;
    }

    if (m_symPathWriter) {
      std::vector<unsigned char> symbolicBranches;
      m_symPathWriter->readStream(m_interpreter->getSymbolicPathStreamID(state),
                                  symbolicBranches);
      llvm::raw_fd_ostream *f = openTestFile("sym.path", id);
      for (std::vector<unsigned char>::iterator I = symbolicBranches.begin(), E = symbolicBranches.end(); I!=E; ++I) {
        *f << *I << "\n";
      }
      delete f;
    }

    if (WriteCov) {
      std::map<const std::string*, std::set<unsigned> > cov;
      m_interpreter->getCoveredLines(state, cov);
      llvm::raw_ostream *f = openTestFile("cov", id);
      for (std::map<const std::string*, std::set<unsigned> >::iterator
             it = cov.begin(), ie = cov.end();
           it != ie; ++it) {
        for (std::set<unsigned>::iterator
               it2 = it->second.begin(), ie = it->second.end();
             it2 != ie; ++it2)
          *f << *it->first << ":" << *it2 << "\n";
      }
      delete f;
    }

    if (m_numGeneratedTests == StopAfterNTests)
      m_interpreter->setHaltExecution(true);

    if (WriteTestInfo) {
      double elapsed_time = util::getWallTime() - start_time;
      llvm::raw_ostream *f = openTestFile("info", id);
      *f << "Time to generate test case: "
         << elapsed_time << "s\n";
      delete f;
    }
  }
}

  // load a .path file
void KleeHandler::loadPathFile(std::string name,
                                     std::vector<bool> &buffer) {
  std::ifstream f(name.c_str(), std::ios::in | std::ios::binary);

  if (!f.good())
    assert(0 && "unable to open path file");

  while (f.good()) {
    unsigned value;
    f >> value;
    buffer.push_back(!!value);
    f.get();
  }
}

void KleeHandler::getKTestFilesInDir(std::string directoryPath,
                                     std::vector<std::string> &results) {
#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
  error_code ec;
#else
  std::error_code ec;
#endif
  for (llvm::sys::fs::directory_iterator i(directoryPath, ec), e; i != e && !ec;
       i.increment(ec)) {
    std::string f = (*i).path();
    if (f.substr(f.size()-6,f.size()) == ".ktest") {
          results.push_back(f);
    }
  }

  if (ec) {
    llvm::errs() << "ERROR: unable to read output directory: " << directoryPath
                 << ": " << ec.message() << "\n";
    exit(1);
  }
}

std::string KleeHandler::getRunTimeLibraryPath(const char *argv0) {
  // allow specifying the path to the runtime library
  const char *env = getenv("KLEE_RUNTIME_LIBRARY_PATH");
  if (env)
    return std::string(env);

  // Take any function from the execution binary but not main (as not allowed by
  // C++ standard)
  void *MainExecAddr = (void *)(intptr_t)getRunTimeLibraryPath;
  SmallString<128> toolRoot(
      llvm::sys::fs::getMainExecutable(argv0, MainExecAddr)
      );

  // Strip off executable so we have a directory path
  llvm::sys::path::remove_filename(toolRoot);

  SmallString<128> libDir;

  if (strlen( KLEE_INSTALL_BIN_DIR ) != 0 &&
      strlen( KLEE_INSTALL_RUNTIME_DIR ) != 0 &&
      toolRoot.str().endswith( KLEE_INSTALL_BIN_DIR ))
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using installed KLEE library runtime: ");
    libDir = toolRoot.str().substr(0,
               toolRoot.str().size() - strlen( KLEE_INSTALL_BIN_DIR ));
    llvm::sys::path::append(libDir, KLEE_INSTALL_RUNTIME_DIR);
  }
  else
  {
    KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                         "Using build directory KLEE library runtime :");
    libDir = KLEE_DIR;
    llvm::sys::path::append(libDir,RUNTIME_CONFIGURATION);
    llvm::sys::path::append(libDir,"lib");
  }

  KLEE_DEBUG_WITH_TYPE("klee_runtime", llvm::dbgs() <<
                       libDir.c_str() << "\n");
  return libDir.str();
}

//===----------------------------------------------------------------------===//
// main Driver function
//
static std::string strip(std::string &in) {
  unsigned len = in.size();
  unsigned lead = 0, trail = len;
  while (lead<len && isspace(in[lead]))
    ++lead;
  while (trail>lead && isspace(in[trail-1]))
    --trail;
  return in.substr(lead, trail-lead);
}

static void parseArguments(int argc, char **argv) {
  cl::SetVersionPrinter(klee::printVersion);
  // This version always reads response files
  cl::ParseCommandLineOptions(argc, argv, " klee\n");
}

static int initEnv(Module *mainModule) {

  /*
    nArgcP = alloc oldArgc->getType()
    nArgvV = alloc oldArgv->getType()
    store oldArgc nArgcP
    store oldArgv nArgvP
    klee_init_environment(nArgcP, nArgvP)
    nArgc = load nArgcP
    nArgv = load nArgvP
    oldArgc->replaceAllUsesWith(nArgc)
    oldArgv->replaceAllUsesWith(nArgv)
  */

  Function *mainFn = mainModule->getFunction(EntryPoint);

  if (!mainFn) {
    klee_error("'%s' function not found in module.", EntryPoint.c_str());
  }

  if (mainFn->arg_size() < 2) {
    klee_error("Cannot handle ""--posix-runtime"" when main() has less than two arguments.\n");
  }

  Instruction *firstInst = &*(mainFn->begin()->begin());

  Value *oldArgc = &*(mainFn->arg_begin());
  Value *oldArgv = &*(++mainFn->arg_begin());

  AllocaInst* argcPtr =
    new AllocaInst(oldArgc->getType(), "argcPtr", firstInst);
  AllocaInst* argvPtr =
    new AllocaInst(oldArgv->getType(), "argvPtr", firstInst);

  /* Insert void klee_init_env(int* argc, char*** argv) */
  std::vector<const Type*> params;
  LLVMContext &ctx = mainModule->getContext();
  params.push_back(Type::getInt32Ty(ctx));
  params.push_back(Type::getInt32Ty(ctx));
  Function* initEnvFn =
    cast<Function>(mainModule->getOrInsertFunction("klee_init_env",
                                                   Type::getVoidTy(ctx),
                                                   argcPtr->getType(),
                                                   argvPtr->getType(),
                                                   NULL));
  assert(initEnvFn);
  std::vector<Value*> args;
  args.push_back(argcPtr);
  args.push_back(argvPtr);
  Instruction* initEnvCall = CallInst::Create(initEnvFn, args,
					      "", firstInst);
  Value *argc = new LoadInst(argcPtr, "newArgc", firstInst);
  Value *argv = new LoadInst(argvPtr, "newArgv", firstInst);

  oldArgc->replaceAllUsesWith(argc);
  oldArgv->replaceAllUsesWith(argv);

  new StoreInst(oldArgc, argcPtr, initEnvCall);
  new StoreInst(oldArgv, argvPtr, initEnvCall);

  return 0;
}


// This is a terrible hack until we get some real modeling of the
// system. All we do is check the undefined symbols and warn about
// any "unrecognized" externals and about any obviously unsafe ones.

// Symbols we explicitly support
static const char *modelledExternals[] = {
  "_ZTVN10__cxxabiv117__class_type_infoE",
  "_ZTVN10__cxxabiv120__si_class_type_infoE",
  "_ZTVN10__cxxabiv121__vmi_class_type_infoE",

  // special functions
  "_assert",
  "__assert_fail",
  "__assert_rtn",
  "calloc",
  "_exit",
  "exit",
  "free",
  "abort",
  "klee_abort",
  "klee_assume",
  "klee_check_memory_access",
  "klee_define_fixed_object",
  "klee_get_errno",
  "klee_get_valuef",
  "klee_get_valued",
  "klee_get_valuel",
  "klee_get_valuell",
  "klee_get_value_i32",
  "klee_get_value_i64",
  "klee_get_obj_size",
  "klee_is_symbolic",
  "klee_make_symbolic",
  "klee_mark_global",
  "klee_open_merge",
  "klee_close_merge",
  "klee_prefer_cex",
  "klee_posix_prefer_cex",
  "klee_print_expr",
  "klee_print_range",
  "klee_report_error",
  "klee_set_forking",
  "klee_silent_exit",
  "klee_warning",
  "klee_warning_once",
  "klee_alias_function",
  "klee_stack_trace",
  "llvm.dbg.declare",
  "llvm.dbg.value",
  "llvm.va_start",
  "llvm.va_end",
  "malloc",
  "realloc",
  "_ZdaPv",
  "_ZdlPv",
  "_Znaj",
  "_Znwj",
  "_Znam",
  "_Znwm",
  "__ubsan_handle_add_overflow",
  "__ubsan_handle_sub_overflow",
  "__ubsan_handle_mul_overflow",
  "__ubsan_handle_divrem_overflow",
};
// Symbols we aren't going to warn about
static const char *dontCareExternals[] = {
#if 0
  // stdio
  "fprintf",
  "fflush",
  "fopen",
  "fclose",
  "fputs_unlocked",
  "putchar_unlocked",
  "vfprintf",
  "fwrite",
  "puts",
  "printf",
  "stdin",
  "stdout",
  "stderr",
  "_stdio_term",
  "__errno_location",
  "fstat",
#endif

  // static information, pretty ok to return
  "getegid",
  "geteuid",
  "getgid",
  "getuid",
  "getpid",
  "gethostname",
  "getpgrp",
  "getppid",
  "getpagesize",
  "getpriority",
  "getgroups",
  "getdtablesize",
  "getrlimit",
  "getrlimit64",
  "getcwd",
  "getwd",
  "gettimeofday",
  "uname",

  // fp stuff we just don't worry about yet
  "frexp",
  "ldexp",
  "__isnan",
  "__signbit",
};
// Extra symbols we aren't going to warn about with klee-libc
static const char *dontCareKlee[] = {
  "__ctype_b_loc",
  "__ctype_get_mb_cur_max",

  // io system calls
  "open",
  "write",
  "read",
  "close",
};
// Extra symbols we aren't going to warn about with uclibc
static const char *dontCareUclibc[] = {
  "__dso_handle",

  // Don't warn about these since we explicitly commented them out of
  // uclibc.
  "printf",
  "vprintf"
};
// Symbols we consider unsafe
static const char *unsafeExternals[] = {
  "fork", // oh lord
  "exec", // heaven help us
  "error", // calls _exit
  "raise", // yeah
  "kill", // mmmhmmm
};
#define NELEMS(array) (sizeof(array)/sizeof(array[0]))
void externalsAndGlobalsCheck(const Module *m) {
  std::map<std::string, bool> externals;
  std::set<std::string> modelled(modelledExternals,
                                 modelledExternals+NELEMS(modelledExternals));
  std::set<std::string> dontCare(dontCareExternals,
                                 dontCareExternals+NELEMS(dontCareExternals));
  std::set<std::string> unsafe(unsafeExternals,
                               unsafeExternals+NELEMS(unsafeExternals));

  switch (Libc) {
  case KleeLibc:
    dontCare.insert(dontCareKlee, dontCareKlee+NELEMS(dontCareKlee));
    break;
  case UcLibc:
    dontCare.insert(dontCareUclibc,
                    dontCareUclibc+NELEMS(dontCareUclibc));
    break;
  case NoLibc: /* silence compiler warning */
    break;
  }

  if (WithPOSIXRuntime)
    dontCare.insert("syscall");

  for (Module::const_iterator fnIt = m->begin(), fn_ie = m->end();
       fnIt != fn_ie; ++fnIt) {
    if (fnIt->isDeclaration() && !fnIt->use_empty())
      externals.insert(std::make_pair(fnIt->getName(), false));
    for (Function::const_iterator bbIt = fnIt->begin(), bb_ie = fnIt->end();
         bbIt != bb_ie; ++bbIt) {
      for (BasicBlock::const_iterator it = bbIt->begin(), ie = bbIt->end();
           it != ie; ++it) {
        if (const CallInst *ci = dyn_cast<CallInst>(it)) {
          if (isa<InlineAsm>(ci->getCalledValue())) {
            klee_warning_once(&*fnIt,
                              "function \"%s\" has inline asm",
                              fnIt->getName().data());
          }
        }
      }
    }
  }
  for (Module::const_global_iterator
         it = m->global_begin(), ie = m->global_end();
       it != ie; ++it)
    if (it->isDeclaration() && !it->use_empty())
      externals.insert(std::make_pair(it->getName(), true));
  // and remove aliases (they define the symbol after global
  // initialization)
  for (Module::const_alias_iterator
         it = m->alias_begin(), ie = m->alias_end();
       it != ie; ++it) {
    std::map<std::string, bool>::iterator it2 =
      externals.find(it->getName());
    if (it2!=externals.end())
      externals.erase(it2);
  }

  std::map<std::string, bool> foundUnsafe;
  for (std::map<std::string, bool>::iterator
         it = externals.begin(), ie = externals.end();
       it != ie; ++it) {
    const std::string &ext = it->first;
    if (!modelled.count(ext) && (WarnAllExternals ||
                                 !dontCare.count(ext))) {
      if (unsafe.count(ext)) {
        foundUnsafe.insert(*it);
      } else {
        klee_warning("undefined reference to %s: %s",
                     it->second ? "variable" : "function",
                     ext.c_str());
      }
    }
  }

  for (std::map<std::string, bool>::iterator
         it = foundUnsafe.begin(), ie = foundUnsafe.end();
       it != ie; ++it) {
    const std::string &ext = it->first;
    klee_warning("undefined reference to %s: %s (UNSAFE)!",
                 it->second ? "variable" : "function",
                 ext.c_str());
  }
}

static Interpreter *theInterpreter = 0;

static bool interrupted = false;


// Pulled out so it can be easily called from a debugger.
extern "C"
void halt_execution() {
  theInterpreter->setHaltExecution(true);
}

extern "C"
void stop_forking() {
  theInterpreter->setInhibitForking(true);
}

static void interrupt_handle() {
  if (!interrupted && theInterpreter) {
    llvm::errs() << "KLEE: ctrl-c detected, requesting interpreter to halt.\n";
    halt_execution();
    sys::SetInterruptFunction(interrupt_handle);
  } else {
    llvm::errs() << "KLEE: ctrl-c detected, exiting.\n";
    exit(1);
  }
  interrupted = true;
}

static void interrupt_handle_watchdog() {
  // just wait for the child to finish
}

// This is a temporary hack. If the running process has access to
// externals then it can disable interrupts, which screws up the
// normal "nice" watchdog termination process. We try to request the
// interpreter to halt using this mechanism as a last resort to save
// the state data before going ahead and killing it.
/*
static void halt_via_gdb(int pid) {
  char buffer[256];
  sprintf(buffer,
          "gdb --batch --eval-command=\"p halt_execution()\" "
          "--eval-command=detach --pid=%d &> /dev/null",
          pid);
  //  fprintf(stderr, "KLEE: WATCHDOG: running: %s\n", buffer);
  if (system(buffer)==-1)
    perror("system");
}
*/
// returns the end of the string put in buf
static char *format_tdiff(char *buf, long seconds)
{
  assert(seconds >= 0);

  long minutes = seconds / 60;  seconds %= 60;
  long hours   = minutes / 60;  minutes %= 60;
  long days    = hours   / 24;  hours   %= 24;

  buf = strrchr(buf, '\0');
  if (days > 0) buf += sprintf(buf, "%ld days, ", days);
  buf += sprintf(buf, "%02ld:%02ld:%02ld", hours, minutes, seconds);
  return buf;
}

#ifndef SUPPORT_KLEE_UCLIBC
static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {
  klee_error("invalid libc, no uclibc support!\n");
}
#else
static void replaceOrRenameFunction(llvm::Module *module,
		const char *old_name, const char *new_name)
{
  Function *f, *f2;
  f = module->getFunction(new_name);
  f2 = module->getFunction(old_name);
  if (f2) {
    if (f) {
      f2->replaceAllUsesWith(f);
      f2->eraseFromParent();
    } else {
      f2->setName(new_name);
      assert(f2->getName() == new_name);
    }
  }
}
static llvm::Module *linkWithUclibc(llvm::Module *mainModule, StringRef libDir) {
  LLVMContext &ctx = mainModule->getContext();
  // Ensure that klee-uclibc exists
  SmallString<128> uclibcBCA(libDir);
  llvm::sys::path::append(uclibcBCA, KLEE_UCLIBC_BCA_NAME);

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 6)
  Twine uclibcBCA_twine(uclibcBCA.c_str());
  if (!llvm::sys::fs::exists(uclibcBCA_twine))
#else
  bool uclibcExists=false;
  llvm::sys::fs::exists(uclibcBCA.c_str(), uclibcExists);
  if (!uclibcExists)
#endif
    klee_error("Cannot find klee-uclibc : %s", uclibcBCA.c_str());

  Function *f;
  // force import of __uClibc_main
  mainModule->getOrInsertFunction(
      "__uClibc_main",
      FunctionType::get(Type::getVoidTy(ctx), std::vector<Type *>(), true));

  // force various imports
  if (WithPOSIXRuntime) {
    llvm::Type *i8Ty = Type::getInt8Ty(ctx);
    mainModule->getOrInsertFunction("realpath",
                                    PointerType::getUnqual(i8Ty),
                                    PointerType::getUnqual(i8Ty),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("getutent",
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("__fgetc_unlocked",
                                    Type::getInt32Ty(ctx),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
    mainModule->getOrInsertFunction("__fputc_unlocked",
                                    Type::getInt32Ty(ctx),
                                    Type::getInt32Ty(ctx),
                                    PointerType::getUnqual(i8Ty),
                                    NULL);
  }

  f = mainModule->getFunction("__ctype_get_mb_cur_max");
  if (f) f->setName("_stdlib_mb_cur_max");

  // Strip of asm prefixes for 64 bit versions because they are not
  // present in uclibc and we want to make sure stuff will get
  // linked. In the off chance that both prefixed and unprefixed
  // versions are present in the module, make sure we don't create a
  // naming conflict.
  for (Module::iterator fi = mainModule->begin(), fe = mainModule->end();
       fi != fe; ++fi) {
    Function *f = &*fi;
    const std::string &name = f->getName();
    if (name[0]=='\01') {
      unsigned size = name.size();
      if (name[size-2]=='6' && name[size-1]=='4') {
        std::string unprefixed = name.substr(1);

        // See if the unprefixed version exists.
        if (Function *f2 = mainModule->getFunction(unprefixed)) {
          f->replaceAllUsesWith(f2);
          f->eraseFromParent();
        } else {
          f->setName(unprefixed);
        }
      }
    }
  }

  mainModule = klee::linkWithLibrary(mainModule, uclibcBCA.c_str());
  assert(mainModule && "unable to link with uclibc");


  replaceOrRenameFunction(mainModule, "__libc_open", "open");
  replaceOrRenameFunction(mainModule, "__libc_fcntl", "fcntl");

  // XXX we need to rearchitect so this can also be used with
  // programs externally linked with uclibc.

  // We now need to swap things so that __uClibc_main is the entry
  // point, in such a way that the arguments are passed to
  // __uClibc_main correctly. We do this by renaming the user main
  // and generating a stub function to call __uClibc_main. There is
  // also an implicit cooperation in that runFunctionAsMain sets up
  // the environment arguments to what uclibc expects (following
  // argv), since it does not explicitly take an envp argument.
  Function *userMainFn = mainModule->getFunction(EntryPoint);
  assert(userMainFn && "unable to get user main");
  Function *uclibcMainFn = mainModule->getFunction("__uClibc_main");
  assert(uclibcMainFn && "unable to get uclibc main");
  userMainFn->setName("__user_main");

  const FunctionType *ft = uclibcMainFn->getFunctionType();
  assert(ft->getNumParams() == 7);

  std::vector<Type *> fArgs;
  fArgs.push_back(ft->getParamType(1)); // argc
  fArgs.push_back(ft->getParamType(2)); // argv
  Function *stub = Function::Create(FunctionType::get(Type::getInt32Ty(ctx), fArgs, false),
                                    GlobalVariable::ExternalLinkage,
                                    EntryPoint,
                                    mainModule);
  BasicBlock *bb = BasicBlock::Create(ctx, "entry", stub);

  std::vector<llvm::Value*> args;
  args.push_back(llvm::ConstantExpr::getBitCast(userMainFn,
                                                ft->getParamType(0)));
  args.push_back(&*(stub->arg_begin())); // argc
  args.push_back(&*(++stub->arg_begin())); // argv
  args.push_back(Constant::getNullValue(ft->getParamType(3))); // app_init
  args.push_back(Constant::getNullValue(ft->getParamType(4))); // app_fini
  args.push_back(Constant::getNullValue(ft->getParamType(5))); // rtld_fini
  args.push_back(Constant::getNullValue(ft->getParamType(6))); // stack_end
  CallInst::Create(uclibcMainFn, args, "", bb);

  new UnreachableInst(ctx, bb);

  klee_message("NOTE: Using klee-uclibc : %s", uclibcBCA.c_str());
  return mainModule;
}
#endif

 void printTASEArgs() {

   printf("TASE args... \n");
   
   if (execMode == MIXED) 
     printf("\t Running MIXED mode (native with interpreter) \n");
   else
     printf("\t Running INTERP_ONLY mode \n");


   printf("Test Type is %s\n", vtt_to_string(verTestType).c_str());
   printf("\t TASE project name: %s \n", project.c_str());
   //Really shouldn't be casting to "bool" below given it's not
   //a defined type for C-style printfs.  Replace with a printstream
   //or something later.
   
   printf("\t taseManager: %d \n", (bool) taseManager);
   printf("\t tasePreProcess  : %d \n", (bool) tasePreProcess);
   printf("\t taseDebug output: %d \n", taseDebug);
   printf("\t bufferGuard output: %d \n", (bool) bufferGuard);
   printf("\t noLog      output: %d \n", (bool) noLog);
   printf("\t dontFork  output: %d \n", (bool) dontFork);
   printf("\t poisonSize: %d \n", (uint8_t) poisonSize);
   printf("\t simdType: %s \n", simdType == XMM ? "XMM" : "YMM");
   printf("\t killFlags      output : %d \n", (bool) killFlags);
   printf("\t skipFree           output : %d \n", (bool) skipFree);
   printf("\t measureTime         output : %d \n", (bool) measureTime);
   printf("\t enableBounceback     output : %d \n", (bool) enableBounceback);
   printf("\t workerSelfTerminate  output : %d \n", (bool) workerSelfTerminate);
   printf("\t dropS2C              output : %d \n", (bool) dropS2C);
   printf("\t enableTimeSeries     output : %d \n", (bool) enableTimeSeries);
   printf("\t retryMax             output : %d \n", (int) retryMax);
   printf("\t tranBBMax            output : %lu \n", (size_t) tran_max);
   printf("\t useCMS4                    output : %d \n", (bool) useCMS4);
   printf("\t useXOROpt                  output : %d \n", (bool) useXOROpt);
   printf("\t UseLegacyIndependentSolver output : %d \n", (bool) UseLegacyIndependentSolver);
   printf("\t UseCanonicalization        output : %d \n", (bool) UseCanonicalization);
   printf("\t optimizeOvershiftChecks    output : %d \n", (bool) optimizeOvershiftChecks);
   printf("\t optimizeConstMemOps        output : %d \n", (bool) optimizeConstMemOps);
 }


 //Load cartridge reference info.
 //This is marked "noinline" in the hope that any stack space used
 //in the initialization can be reclaimed before we transfer to the
 //analysis target and get stuck dealing with it across forks.

 void __attribute__((noinline)) loadCartridgeInfo()  {
   LOG_TASE("Detected %lu basic block records when loading cartridge info \n", tase_num_global_records);
   
   //Load the start addresses of cartridges for fast lookup later
   for ( uint32_t i = 0; i < tase_num_global_records; i++ )  {
     cartridge_heads.insert(tase_global_records[i].head);
     cartridge_entry_points.insert( tase_global_records[i].head + tase_global_records[i].head_size );
     // should this use head or head + head_size ? 
     cartridge_regstatus.insert( {tase_global_records[i].head + tase_global_records[i].head_size, {tase_global_records[i].reg_deadness, tase_global_records[i].live_ins } } );

     if( tase_global_records[i].kill_flags ) 
       kill_flags.insert( tase_global_records[i].head );
   }

   LOG_TASE("found %ld cartridge entry points, %ld locations with dead flags\n", cartridge_entry_points.size(), kill_flags.size());
   // int numLiveBlocks = 0;
   // for (uint32_t i = 0; i < tase_num_live_flags_block_records; i++) {
   //   cartridges_with_flags_live.insert(tase_live_flags_block_records[i].head + tase_live_flags_block_records[i].head_size);
   //   numLiveBlocks++;
   // }
   // LOG_TASE("Found %d basic blocks with flags live-in \n", numLiveBlocks);
   /*   for( uint32_t i = 0; i < tase_num_kill_flags_block_records; ++i) {
     kill_flags.insert(tase_kill_flags_block_records[i]);
     }*/
 }


//Make seperate directories for each of the workers in the time series.
 void makeTSPath(int trace_ID) {
   //TODO -- merge in ssl verification code
  
 }


 bool isTimeSeriesDone() {
   //TODO -- merge in ssl verification code
   return true;
 }


 void __attribute__ ((noreturn)) transferToTarget(int argc, char** argv)  {
   run_start_time = util::getWallTime();
   
   LOG_TASE("Inside transferToTarget\n")

   if (execMode == INTERP_ONLY) {    
     klee_interp();
   } else {
     
     tase_inject();

     DBG_TASE("Returning from tase_inject...\n");
     
     while (true) {
       klee_interp();

       DBG_TASE("Returning from klee_interp at %lx\n", target_ctx_gregs[GREG_RIP].u64)
       
       tase_inject();
       
       DBG_TASE("Returning from tase_inject...\n");
     }
   }
 }


 //Attempt to load basic block successor information for basic blocks ending in
 //non-indirect control flow (e.g., je, jne, etc).  Information goes into
 //"knownCartridgeDests" to give solver a hint when encountering symbolic
 //RIP values after certain basic blocks.
//For tetrinet
void populatePieceInfo();
void printPieceInfo();

 //This can be generalized and automated within the compiler, but for now
 //it's a manual process. 
 void __attribute__((noinline)) loadCartridgeDests() {

   //TODO
   
 }

 bool tetriTest = true;
 extern void printTetriNETLogs();
 extern void loadTetriNETLogs(std::string fileName);
 extern std::string next_msg_to_verify;
 enum TetriNETMsgType_t  {
			                           puC2S, sbC2S, lvlC2S, otherC2S, S2C, INPUT
			   };
 struct TetriNETLogRecord {
     enum TetriNETMsgType_t type;
     std::string msg;
     double timeStamp;
   };
 double postInitStartTime; //Timestamp for measuring runtimes after initialization is completed.
// In a real-world verification scenario, we envision a verifier (or several of them)  performing
//the initialization to prepare for for verification prior to later being assigned a connection to rapidly
//verify in realtime.  So we exclude the initialization costs (e.g., loading bitcode) with this timestamp.
extern void loadBestMessageBranchMap( const char * logName);
 extern struct TetriNETLogRecord peekNthC2SPartialUpdate(int n);
extern  void initializeEditDistanceOracle_medoid2Msgs(std::string processedTrainingDataPath ); 
 int main (int argc, char **argv, char **envp) {
   signal(SIGSTD, SIG_IGN);//
   printf("TASE LAUNCHED \n");
   fflush(stdout);

   memset(&target_ctx, 0, sizeof(target_ctx));
   signal(SIGCHLD, SIG_IGN);
   signal(SIGRTMIN+1, SIG_IGN);
   signal(SIGRTMIN+2, SIG_IGN);
   signal(SIGRTMIN+3, SIG_IGN);
   setpgid(0, 0);
   
   glob_argc = argc;
   glob_argv = argv;
   glob_envp = envp;
   
   llvm::InitializeNativeTarget();
   parseArguments(argc, argv);

   logFile = logFileArg;
   
   taseLog = logFile == "false" ? NULL : fopen(logFile.c_str(), "w");
   
   if ( verTestType != VerTestType::EXPLORATION ) {
     DBG_TASE("Enabling multipass verification for openssl \n")
     enableMultipass = true;
   }

   
   rsp_global = target_ctx.rsp.u64;   
   taseDebug = taseDebugArg;
   sleepDbgUs = sleepDbgUsArg;
   //   modelDebug = modelDebugArg;
   localStack = abs(taseLocalStack);
   bufferGuard = bufferGuardArg;
   dropS2C = dropS2CArg;
   enableTimeSeries = enableTimeSeriesArg;

   singleStepping = (bool) singleSteppingArg;
   killFlags = singleStepping ? false : killFlags;
   ex_state = EXECUTION_STATE((bool) execMode == MIXED, (bool)singleSteppingArg, (bool) enableBounceback);
   
   //If we don't explicitly give the project name, use some defaults.
   //This is particularly useful when running TASE from the projects directory because
   //it removes the number of args needed to launch TASE.
   if ( strcmp(project.c_str(), "-") == 0 ) {
     char pathBuf [512];
     getcwd(pathBuf, 512);
     std::string path (pathBuf);
     size_t idx = path.find_last_of('/');
     std::string currDir = path.substr(idx + 1, std::string::npos);

     project=currDir;

     //Also, load the bitcode
     InputFile = path + "/bitcode/" + project + ".interp.bc";     
   } else {
     char pathBuf[512];
     getcwd(pathBuf, 512);
     std::string path (pathBuf);
     InputFile = path + "/bitcode/" + project + ".interp.bc";
   }
	        

   tranMaxArg = (uint64_t) tranMaxArgInp;
   tran_max = tranMaxArg;
   trap_off = (uint64_t) trapOffset;
   MAX_RUNNING_WORKERS = (size_t) maxRunning;
   MAX_STOPPED_WORKERS = (size_t) maxStopped;
   LOG_TASE("Max Running: %ld, Max Stopped: %ld\n", MAX_RUNNING_WORKERS, MAX_STOPPED_WORKERS);LOG_FLUSH();
   clientNameExternal = (std::string) clientName;
   editDistanceOracleClusters = (std::string) editDistanceOracleClustersArg;
   singleMsgVerificationIdx = (int) singleMsgVerificationIdxArg;
   tetrinetLog = (std::string) tetrinetLogArg;
   cacheMLPreds = (bool) cacheMLPredsArg;
   zeroMLMH = (bool) zeroMLMHArg;
   msgsInPrevMsgWindow = (int) msgsInPrevMsgWindowArg;


   branchLimitForPriorityDecay = (int) branchLimitForPriorityDecayArg;
   priorityDecayFactor = (double) priorityDecayFactorArg;

   fixMH = (bool) fixMHArg;
   useMHWindow = (bool) useMHWindowArg;
   useMHWindowEdges = (bool) useMHWindowEdgesArg;
   useMHWindowCoords = (bool) useMHWindowCoordsArg;
   MHWindowSize = (int) MHWindowSizeArg;
   useMsgFeatsInJoint = (bool) useMsgFeatsInJointArg;
   oracleFilePath = (std::string) pathOracleFilePath;
   jointOracleFilePath = (std::string) jointOracleFilePathArg;
   secondJointOracleFilePath = (std::string) secondJointOracleFilePathArg;
   thirdJointOracleFilePath = (std::string) thirdJointOracleFilePathArg;

   secondMHOracleFilePath = (std::string) secondMHOracleFilePathArg;
   thirdMHOracleFilePath = (std::string) thirdMHOracleFilePathArg;
   
   pathHistoryOracleFilePath = (std::string) pathHistoryOracleFilePathArg;
   secondPathHistoryOracleFilePath = (std::string) secondPathHistoryOracleFilePathArg;
   thirdPathHistoryOracleFilePath = (std::string) thirdPathHistoryOracleFilePathArg;

   messageHistoryOracleFilePath = (std::string) mhOracleFilePathArg;
   useFFOracle = (bool) useFFOracleArg;
   pathAndMHOracleWithCoords = (bool) pathAndMHOracleWithCoordsArg; 
   useLEARCHFeatsOracle = (bool) useLEARCHFeatsOracleArg;
   numberOfOracles = (int) numberOfOraclesArg;

   useFallBackOracle = (bool) useFallBackOracleArg;
   fallBackBranchThreshold = (int) fallBackBranchThresholdArg;
   fallbackOracleActive = false;
   multiOracleUseMessageHistoryOracle = (bool) multiOracleUseMessageHistoryOracleArg;
   useAveragedOracles = (bool) useAveragedOraclesArg;
   useCoordsWithoutMH = (bool) useCoordsWithoutMHArg;
   useBBForDense = (bool) useBBForDenseArg;
   BBForDenseAndNoMH = (bool) BBForDenseAndNoMHArg;
   BBForDenseAndLSTMMH = (bool) BBForDenseAndLSTMMHArg;
   //NEW
   //LOG_TASE("Trying load medoid map \n");LOG_FLUSH();
   //initializeEditDistanceOracle_medoid2Msgs("../medoid2MsgsMap");  //PICK UP HERE

   ////////
   
   if (!tasePreProcess) {
     printTASEArgs();
   } else {
     printf("Running TASE preprocessing... \n");fflush(stdout);
     
     FILE * cartridgeLog = fopen("cartridge_info.txt", "w");
     for (uint32_t i = 0; i < tase_num_global_records; i++) {
       uint32_t head = tase_global_records[i].head;
       uint16_t head_size = tase_global_records[i].head_size;
       uint16_t body_size = tase_global_records[i].body_size;
       int32_t reg_deadness = tase_global_records[i].reg_deadness;
       int32_t live_ins = tase_global_records[i].live_ins;
       bool kill_flags = tase_global_records[i].kill_flags;
       fprintf(cartridgeLog, "%x %x %x %x %s (head: %x)\n", head + head_size, head + head_size + body_size, reg_deadness, live_ins, kill_flags ? "1" : "0", head);
     }
     fclose(cartridgeLog);
     printf("Finished TASE preprocessing \n");
     fflush(stdout);
     std::exit(EXIT_SUCCESS);
   }

   // Load the bytecode...
   std::string errorMsg;
   LLVMContext ctx;

   DBG_TASE("Attempting to load bitcode from %s\n", InputFile.c_str())
   auto bcloadtime = util::getWallTime();
   
   interpModule = klee::loadModule(ctx, InputFile, errorMsg);

   DBG_TASE("Bitcode module has been loaded...\n");
   
   if (!interpModule) {
    klee_error("error loading program '%s': %s", InputFile.c_str(),
               errorMsg.c_str());
  }

  LOG_TASE("Bitcode load took %f seconds\n", util::getWallTime() - bcloadtime)
  ///////////////////////Arg Parsing section

   int pArgc;
   char **pArgv;
   char **pEnvp;
   if (Environ != "") {
     std::vector<std::string> items;
     std::ifstream f(Environ.c_str());
     if (!f.good())
       klee_error("unable to open --environ file: %s", Environ.c_str());
     while (!f.eof()) {
       std::string line;
       std::getline(f, line);
       line = strip(line);
       if (!line.empty())
	 items.push_back(line);
     }
     f.close();
     pEnvp = new char *[items.size()+1];
     unsigned i=0;
     for (; i != items.size(); ++i)
       pEnvp[i] = strdup(items[i].c_str());
     pEnvp[i] = 0;
   } else {
     pEnvp = envp;
   }

   LOG_TASE("InputArgv: \n")
   std::string pname = std::string(&tase_progname[0], strlen(tase_progname));
   LOG_TASE("  %s\n", tase_progname)
   for(auto& x : InputArgv){
     LOG_TASE("  %s\n", x.c_str())
   }

   if( poisonSize == WORD ) {
     target_ctx.poisonSize = 2;
     if( simdType == XMM ) {
       large_buf_has_taint = large_buf_has_taint_16_128;
     } else {
       large_buf_has_taint = large_buf_has_taint_16_256;
     }
   } else {
     target_ctx.poisonSize = 4;
     if( simdType == XMM ) {
       large_buf_has_taint = large_buf_has_taint_32_128;
     } else {
       large_buf_has_taint = large_buf_has_taint_32_256;
     }
   }

   
   std::vector<size_t> argsizes;
   pArgc = InputArgv.size() + 1;
   pArgv = new char *[pArgc];
   for (unsigned i=0; i<InputArgv.size()+1; i++) {
     std::string &arg = ( i == 0 ? pname : InputArgv[i-1] );
     LOG_TASE("Arg: %s\n", arg.c_str())
     unsigned size = arg.size() + 1;
     char *pArg = new char[size];
     argsizes.push_back((size_t) size);
     std::copy(arg.begin(), arg.end(), pArg);
     pArg[size - 1] = 0;
     pArgv[i] = pArg;
   }
   ///////////////////// End of Arg Parsing Section

   LOG_TASE("Creating interpreter... \n")
   Interpreter::InterpreterOptions IOpts;
   KleeHandler *handler = new KleeHandler(pArgc, pArgv);
   Interpreter *interpreter =
     theInterpreter = Interpreter::create(ctx, IOpts, handler);
   handler->setInterpreter(interpreter);

   std::string LibraryDir = KleeHandler::getRunTimeLibraryPath(argv[0]);
   Interpreter::ModuleOptions Opts(LibraryDir.c_str(), EntryPoint,
                                  /*Optimize=*/OptimizeModule,
                                  /*CheckDivZero=*/CheckDivZero,
                                  /*CheckOvershift=*/CheckOvershift);

   interpreter->setModule(interpModule, Opts);

   //ABH: Entry fn for our purposes is a dummy main function.
   // It's specified in parseltongue86 as dummyMain and
   // as_Z9dummyMainv in "EntryPoint" because of cpp name mangling.  
   Function *entryFn = interpModule->getFunction(EntryPoint);
   if (!entryFn){
     LOG_TASE("ERROR: Couldn't locate entryFn \n")
     std::exit(EXIT_FAILURE);
   }

   DBG_TASE("Initializing interpretation structures ...\n")
     
   LOG_TASE("Total named md, funcs, aliases, ifuncs: %ld, %ld, %ld \n", interpModule->named_metadata_size(),
	  interpModule->size(), interpModule->alias_size());
     
   interpModule->named_metadata_empty();
   LOG_TASE("Calling initializeInterpretationStructures")
   
   interpreter->initializeInterpretationStructures(entryFn);
   GlobalInterpreter = interpreter;
   
   LOG_TASE("Calling loadCartridgeInfo \n");
   loadCartridgeInfo();
   
#ifdef TASE_OPENSSL

   char * ktestModeName = "-playback";
   memset(ktestMode, 0, sizeof (ktestMode));
   strncpy(ktestMode, ktestModeName, strlen(ktestModeName));

   memset(ktestPath, 0, sizeof(ktestPath));

   if (enableTimeSeries) {
     LOG_TASE("ERROR: Need to reintegrate code for time series \n")
     LOG_FLUSH()
     std::exit(EXIT_FAILURE);
     //spawnTimeSeriesWorkers();
   } else {
     
     const char *  ktestPathName = verificationLog.c_str();
     strncpy(ktestPath, ktestPathName, strlen(ktestPathName));
   }
   
   #endif
   //--------

   #ifdef TASE_OPENSSL

   if (!enableTimeSeries) {
     sleep(10); //Let khugepaged catch up before we launch
   }

   #endif // TASE_OPENSSL

   double theTime = util::getWallTime();
   target_start_time = theTime;  //Moved here to initialize for both manager and workers
   last_message_verification_time = theTime;
   

   signal(SIGCHLD, SIG_IGN);
   
   int res = prctl(PR_SET_CHILD_SUBREAPER, 1);
   if (res == -1) {
     //     perr("Initial prctl error ");
     LOG_TASE("Initial prctl error ")
     exit(EXIT_FAILURE);
   }
   LOG_TASE("Calling init_structures \n");
   init_structures();
   LOG_TASE("Calling setup_client\n"); LOG_FLUSH();
   setup_client();  //Load client-specific logs, add client-specific traps
   if (verTestType == VerTestType::TRAIN) {
     initSharedMLIDMem();
   }
   
   print_mavlink_msgs();//DBG, remove me later
   if (verTestType == VerTestType::TRAIN && clientName == "MAVLINK" ) {
     loadMavlinkTrainingCluster(); //Move to setup_client() later
     msgCtr = (int) klee::singleMsgVerificationIdx;
     //initSharedMLIDMem();
   }
   LOG_TASE("Returned from loadMavlinkTrainingCluster \n"); LOG_FLUSH();
   //LOG_FLUSH();
   //exit(0);
   
   if (clientName == "TETRINET") {
     populatePieceInfo();
     printPieceInfo();
   }
   fflush(stdout);
   LOG_FLUSH();
   LOG_TASE("Calling initial_fork \n");
   LOG_FLUSH();
   //testPQ(20);
   //testBFS();
   //testDFS();
   if ( (verTestType == VerTestType::SINGLEMSGVER) && updateSyntheticPaths) {
     if (initialMessageBranchMapFile == "NONE") {
       LOG_TASE("ERROR: Populate file path for initialMessageBranchMapFile \n");LOG_FLUSH();
       exit(0);
     }
     loadBestMessageBranchMap(initialMessageBranchMapFile.c_str());
   }
   
   int pid = initial_fork();

   if (pid != 0 ) {
     // if (explorationType == TASEExplorationType::ML) {
     //   printf("Setting up ml oracle in manager pid %d \n", getpid());fflush(stdout);
     //   setup_ml_oracle(pathOracleFilePath.c_str());
     //   printf("Loaded oracle \n");fflush(stdout);
     //   double warmUpStartTime = util::getWallTime();
     //   warm_up_ml_oracle(); //Force the oracle to initialize everything by doing a dummy calc
     //   printf ("Spent %lf seconds on warmup for ml oracle \n",util::getWallTime() - warmUpStartTime);fflush(stdout);
     // } else if (explorationType == TASEExplorationType::ED)   {
     //   printf("Attempting to load cluster info \n");fflush(stdout);
     //   initializeEditDistanceOracle(editDistanceOracleClusters);
     //   printf("Loaded clusterMap \n");fflush(stdout);
     // }
     if (verTestType != VerTestType::REPLAY) {
       if (explorationType == TASEExplorationType::ED && ( (verTestType == VerTestType::VERIFY) || (verTestType == VerTestType::SINGLEMSGVER) )  ) {
	 //NEW
	 LOG_TASE("Trying load medoid map \n");LOG_FLUSH();
	 initializeEditDistanceOracle_medoid2Msgs("../medoid2MsgsMap");  //PICK UP HERE
       }
       if (explorationType == TASEExplorationType::ED || explorationType == TASEExplorationType::ML) {
	 if (useMLMH) {
	   init_oracle_mh();

	   if (verTestType == VerTestType::SINGLEMSGVER) {
	     if (useMHWindow || useMHWindowEdges || useMHWindowCoords || useFFOracle) {
	       //nothing to do.  We'll make the window during inference.
	     } else {

	       if (msgsInPrevMsgWindowArg >= 0) {
		 setup_prev_mh_window((int) klee::singleMsgVerificationIdx, (int) msgsInPrevMsgWindowArg);
	       } else {
		 update_mh_singleMsgVerify((int) klee::singleMsgVerificationIdx);
	       }
	     }
	   }
	 } else {
	   init_oracle();
	 }
       }
       LOG_TASE("DBG 11 \n");LOG_FLUSH();
       if (printMHVecsAndExitArg) {
	 LOG_TASE("DBG 22 \n");LOG_FLUSH();
	 calcMHVecsAndExit();
       }
       LOG_TASE("DBG 33 \n");LOG_FLUSH();

     }
   }

   
   
   postInitStartTime = util::getWallTime();
   
   if (pid == 0){
     orig_stdout_fd = dup(STDOUT_FILENO); //Backup stdout fd so that we can grab control later.
     uint64_t orig_stdout = (uint64_t) stdout; 
     worker_ID_stream << ( logFile == "false" ? "Monitor" : logFile ) << ".stdout." << getpid();

     // not a mistake, we want w+ here so we don't have to close/reopen to
     // do a sendfile in cycleTASELogs

     prev_stdout_log = freopen(worker_ID_stream.str().c_str(), "w+", stdout);

     if( logFile != "false" ) {
       std::string mon = logFile + "." + std::to_string(getpid());
       taseLog = fopen(mon.c_str(), "w");
     }
     
     if (prev_stdout_log == NULL) {
       LOG_TASE("FATAL ERROR redirecting stdout \n")
	 std::exit(EXIT_FAILURE);
     }
     
     LOG_TASE("worker stdout: %lx, orig: %lx\n----------------SWAPPING TO TARGET CONTEXT------------------ \n", (uint64_t) stdout, orig_stdout)     
           
     auto exe = static_cast<klee::Executor*>(interpreter);
     exe->tase_map(saved_rax, "saved_rax");
     exe->tase_map(rsp_global, "rsp_global");
     for(int i = 0; i < pArgc; ++i){
       if ( i > 0 ) {
         LOG_TASE("mapping arg: %s, size: %ld\n", pArgv[i], strlen(pArgv[i])+1);	 

	 int roundedUpSize;
	 if ( (strlen(pArgv[i]) +1) %8 == 0)
	   roundedUpSize = strlen(pArgv[i]) +1;
	 else {
	   roundedUpSize = ((strlen(pArgv[i]) +1)/8 ) * 8 + 8;
	 }
	 LOG_TASE("Rounded up size is %d \n", roundedUpSize);LOG_FLUSH();
	 
	 //exe->tase_map(pArgv[i], strlen(pArgv[i]) + 1, "pArgv[" + std::to_string(i) + "]");
	 exe->tase_map(pArgv[i], roundedUpSize, "pArgv[" + std::to_string(i) + "]"); //Is this still needed?
       }
     }

     init_tase_ctx(begin_target_inner, pArgc, pArgv);
     cartridge_rip = (uint64_t) &begin_target_inner;
   
     LOG_TASE("Initial Context:\n")
     exe->printCtx();
   
     if (taseDebug)
       LOG_TASE("Calling transferToTarget()\n");

     transferToTarget(pArgc, pArgv);
     LOG_TASE("RETURNING TO MAIN HANDLER \n")
       } else {
     LOG_TASE("Manager is pid %d \n", getpid()); LOG_FLUSH();
     printf("Manager is pid %d \n", getpid());fflush(stdout);
     manage_workers();
   }
 }
