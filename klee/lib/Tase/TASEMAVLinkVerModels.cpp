
#include "../Core/Executor.h"
#include "../Core/Context.h"
#include "../Core/CoreStats.h"
#include "../Core/ExternalDispatcher.h"
#include "../Core/ImpliedValue.h"
#include "../Core/Memory.h"
#include "../Core/MemoryManager.h"
#include "../Core/PTree.h"
#include "../Core/Searcher.h"
#include "../Core/SeedInfo.h"
#include "../Core/SpecialFunctionHandler.h"
#include "../Core/StatsTracker.h"
#include "../Core/TimingSolver.h"
#include "../Core/UserSearcher.h"
#include "../Core/ExecutorTimerInfo.h"

#include "klee/ExecutionState.h"
#include "klee/Expr.h"
#include "klee/Interpreter.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/CommandLine.h"
#include "klee/Common.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/GetElementPtrTypeIterator.h"
#include "klee/Config/Version.h"
#include "klee/Internal/ADT/KTest.h"
#include "klee/Internal/ADT/RNG.h"
#include "klee/Internal/Module/Cell.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/KModule.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FloatEvaluation.h"
#include "klee/Internal/Support/ModuleUtil.h"
#include "klee/Internal/System/Time.h"
#include "klee/Internal/System/MemoryUsage.h"
#include "klee/SolverStats.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/raw_ostream.h"

#if LLVM_VERSION_CODE < LLVM_VERSION(3, 5)
#include "llvm/Support/CallSite.h"
#else
#include "llvm/IR/CallSite.h"
#endif

#ifdef HAVE_ZLIB_H
#include "klee/Internal/Support/CompressionStream.h"
#endif

#include <sys/resource.h>
#include <cassert>
#include <algorithm>
#include <iomanip>
#include <iosfwd>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <sys/mman.h>
#include <errno.h>
#include <cxxabi.h>
#include <iostream>
#include "klee/CVAssignment.h"
#include "klee/util/ExprUtil.h"
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <netdb.h>
#include <fcntl.h>
#include "tase_interp.h"
#include "tase_shims.h"
#include "tase/TASEControl.h"
#include "../Tase/TASESoftFloatEmulation.h"
#include <sys/times.h>
#include <sys/time.h>
#include <unordered_set>
#include <iconv.h>
#include <ifaddrs.h>
#include <signal.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <arpa/inet.h>
//#include <gnutls/crypto.h>
#include <pwd.h>
#include <pthread.h>
#include <sys/epoll.h>
#include <libgen.h>
#include <sys/mman.h>
#include <zlib.h>
#include <sys/wait.h>

//ADAM MERGE NOTES:
//Move over priority/greedy lstm logic manually
//
//Need to move over Executor.h as well
//Also code from main.cpp and link.txt
//Also tensorflow stuff if necessary
std::vector<uint64_t> loadedMavlinkTrainingBBIDs;
int currMavlinkTrainingBBIDIdx =0;

#include <curses.h>
#include "tase/EditDistanceOracle.h"
#include "tase/TASEConstraintBOWEncoding.h"
#include "ClientWorkerFeats.h"
#include "API.h"
extern FILE * cluster_log;
//#include "WorkerInfo.h"
//#include "WorkerGroup.h"
//extern void worker_success(struct WorkerGroup * Stopped, struct WorkerGroup * Running);

using namespace llvm;
using namespace klee;

//TASE internals--------------------
extern uint16_t poison_val;
extern target_ctx_t target_ctx;
extern tase_greg_t * target_ctx_gregs;
extern int taseDebug;
extern int retryMax;
extern Module * interpModule;
extern klee::Interpreter * GlobalInterpreter;
extern std::unordered_set<uint64_t> cartridge_entry_points;
extern std::unordered_set<uint64_t> cartridges_with_flags_live;
extern double target_start_time;
extern double target_end_time;
extern Executor * GlobalExecutorPtr;
extern MemoryObject * target_ctx_gregs_MO;
extern ObjectState * target_ctx_gregs_OS;
extern ExecutionState * GlobalExecutionStatePtr;
extern uint64_t interpCtr;
//extern uint64_t concInterpCtr;
extern int branchDepth = 0;
//extern void worker_exit(int);
//extern bool modelDebug;
extern bool inForkElisionReplay;

extern int stats_branches;
extern int branchType;
extern int last_IR_branch_type;
extern bool logBadBranch;
extern uint64_t pre_interp_RIP;
//uint64_t preBranchBB;

extern uint64_t getMLBBID (uint64_t rip);
extern uint64_t getMLBBIDWithIR(uint64_t rip, int IRBranchIdx);
extern FILE * featLog;
extern FILE * replayFile;
extern int msgCtr;
extern bool inTestBranch;
extern std::string verMsg;
extern std::string nextC2SMsg;
extern bool inPriorityTest;// Variable to determine if we're currently forking off a worker for the priority test
extern double priorityRunStart;

extern "C" void workerResetFeats();

extern int tase_fork_IR(uint64_t trueBranchID, uint64_t falseBranchID, std::vector<std::vector<float>> IR_Constraint_BOWs);
extern int tase_fork_RIP(std::vector<uint64_t> dests, std::vector<std::vector<float>> RIP_Constraint_BOWs);
//std::string clusterStartType = "ENTRY";  //Valid Types: ENTRY, SEND or SELECT (no select in our TetriNET)
extern std::string clusterEndType;  //Valid Types: SEND (removed RECV)
void resetAndWriteCluster(void * msg, size_t msgSize, std::string clusterLogName);
extern std::map<int,int> initialMessageBranchMap;
extern std::map<int, int> bestMessageBranchMap;
void printMessageBranchMap(std::map<int,int> mapping, FILE * output);
extern void * prevLogMsgs;
extern int prevLogMsgsSize;
extern void * nextLogMsgs;
extern int nextLogMsgsSize;

extern bool onValidPath;
extern int badBranchDepth;
extern int maxBadBranchDepth;
extern int getNewMLID();
extern std::string pathOracleFilePathArg;
extern double updateLSTMPred(int x, int y, int rot, uint64_t branchesSinceLastMsg, uint64_t BBID);
extern double peekLSTMPred (int x, int y, int rot, uint64_t branchesSinceLastMsg, uint64_t BBID);

extern std::vector<uint64_t> execution_fragment; //duplicated with BBBOWVec
//extern uint64_t branchesSinceLastMsg;
uint64_t branchesSinceLastMsg =0 ;

namespace klee {
  extern int singleMsgVerificationIdx;
  extern bool useFallBackOracle;//Determine if we need to fall back to another oracle after a certain threshold is reached
  extern int fallBackBranchThreshold;//Fall back to the second oracle if we fail to verify in branches less than or equal to this number
  extern bool fallbackOracleActive;
  extern bool useCoordsWithoutMH;
  extern bool useLEARCHFeatsOracle;
};

extern "C" void resetBranches();
extern "C" void addBranch();
extern "C" void clearExecutionFragment();

extern UFManager *ufmanager;
extern UFManager *ufmanager_cheat;

extern bool makeInitialBranchMap;
extern int MLParentID;
#include "MAVLinkProcessedPackets.c"
#include "mavlink.h"
std::vector<std::vector<uint8_t>> mavlinkMsgs;
std::vector<double> mavlinkMsgTimes;
extern int msgCtr;
int currMsgVerIdx = 0;
std::vector<uint8_t> getCurrMsgToVerifyMavlink();
int getCurrMsgIdxMavlink();
extern "C" int getBranchesSinceLastMsg();
uint64_t getMavlinkMsgType(int i );

//Format: MSG SIZE:X
//MSG:
//FRAGS:

extern std::string clusterEndType;
//Over and over...
void resetAndWriteCluster(void * msg, size_t msgSize, std::string clusterLogName) {
  static int callCtr = 0;

  if (callCtr == 0) {
    cluster_log = fopen(clusterLogName.c_str(), "w+");
  }
  callCtr++;

  uint8_t * bytePtr = (uint8_t *) msg;
  //MSG  
  for (int i = 0; i < msgSize; i++) {
    fprintf(cluster_log, "%x,", *bytePtr);
    bytePtr++;
  }
  fprintf(cluster_log,"\n");
  //Type
  fprintf(cluster_log, "%lu,", execution_fragment[0]); //This is the first branch dest from a symbolic branch
  fprintf(cluster_log, "%s,", clusterEndType.c_str());
  fprintf(cluster_log, "\n");
  //BBs
  for (int i = 0; i < execution_fragment.size(); i++) {
    fprintf(cluster_log, "%lu,", execution_fragment[i]);
  }
  fflush(cluster_log);
  fprintf(cluster_log,"\n");
  //Constraints
  //(skipped for now)

  fprintf(cluster_log,"\n");
  fflush(cluster_log);
  execution_fragment.clear();
  LOG_TASE("Leaving resetAndWriteCluster \n");LOG_FLUSH();
}

void load_mavlink_msgs() {
  LOG_TASE("Entering load_mavlink_msgs()");LOG_FLUSH();
  std::ifstream logFile(mavlinkLog);

  if (logFile.is_open()) {
    LOG_TASE("MAVLink FILE is open \n");LOG_FLUSH();
  } else {
    LOG_TASE("ERROR: MAVLink FILE isn't open \n");LOG_FLUSH();
    exit(0);
  }
  
  std::string currLine;
  //Get timestamp on one line, then msg bytes on next
  while(std::getline(logFile, currLine)) {
    if (currLine == "") {
      LOG_TASE("Hit empyty line at end of file \n");LOG_FLUSH();
      break;
    }
    double time = std::stod(currLine);
    mavlinkMsgTimes.push_back(time);
    
    //Get the bytes
    std::getline(logFile, currLine);
    
    //Tokenize by spaces within the line
    std::vector<uint8_t> msgBytes;
    std::string currByteStr;
    std::stringstream currLineStream(currLine);
    while (getline(currLineStream, currByteStr, ' ')) { //Does the tokenizing
      uint8_t b = (uint8_t) stoi(currByteStr, NULL, 16);
      msgBytes.push_back(b);
    }
    mavlinkMsgs.push_back(msgBytes);
  }
  LOG_TASE("Loaded %d mavlink msgs \n", mavlinkMsgs.size());
  logFile.close();
  
}

void print_mavlink_msgs() {
  int max_msg_size = 0;
  for (int i = 0 ; i < mavlinkMsgs.size(); i++) {
    if (i < (int) singleMsgVerificationIdx ) {
      continue;
    }
    LOG_TASE("---------------------------\n");LOG_FLUSH();
    LOG_TASE("MSG %d  TIME    : %lf \n", i, mavlinkMsgTimes[i]);LOG_FLUSH();
    LOG_TASE("MSG %d  BYTES   : ", i);
    
    std::vector<uint8_t> currMsg = mavlinkMsgs[i];
    for (int j = 0; j < currMsg.size(); j++){
      LOG_TASE("%02X ", currMsg[j]);
    }
    LOG_TASE("\n");
    LOG_TASE("MSG %d  SIZE    :  %d \n",i, currMsg.size());
    LOG_TASE("MSG %d  MSG TYPE: %d\n",i, getMavlinkMsgType(i));
    LOG_FLUSH();
    if (currMsg.size() > max_msg_size) {
      max_msg_size = currMsg.size();
    }
  }
}

void mavlink_write_tase(int fd, void * buf, size_t count);
extern void printBuf(FILE * f, void * buf, size_t count);
void Executor::model_mavlink_write_tase() {
  double T0 = util::getWallTime();
  LOG_TASE("Entering model_mavlink_write_tase \n");

  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);
  if (!isa<ConstantExpr> (arg1Expr)) {
    LOG_TASE("Arg1 not constant \n"); LOG_FLUSH();
    ExecutionState dummy = ExecutionState(getDepCons(arg1Expr,false));
    std::vector<ref<Expr>> destExprs = getNPossibleValues(dummy, arg1Expr, 100);
    LOG_TASE("Found %d vals for arg \n", destExprs.size());LOG_FLUSH();
    if (destExprs.size() == 1) {
      arg1Expr = destExprs[0];
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDI], destExprs[0]);
    }
  }
  if (!isa<ConstantExpr> (arg2Expr)) {
    LOG_TASE("Arg2 not constant \n"); LOG_FLUSH();
    ExecutionState dummy = ExecutionState(getDepCons(arg2Expr,false));
    std::vector<ref<Expr>> destExprs = getNPossibleValues(dummy, arg2Expr, 100);
    LOG_TASE("Found %d vals for arg \n", destExprs.size());LOG_FLUSH();
    if (destExprs.size() == 1) {
      arg2Expr = destExprs[0];
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RSI], destExprs[0]);
    }
  }

  if (!isa<ConstantExpr> (arg3Expr)) {
    LOG_TASE("Arg3 not constant \n"); LOG_FLUSH();
    ExecutionState dummy = ExecutionState(getDepCons(arg3Expr,false));
    std::vector<ref<Expr>> destExprs = getNPossibleValues(dummy, arg3Expr, 100);
    LOG_TASE("Found %d vals for arg \n", destExprs.size());LOG_FLUSH();
    if (destExprs.size() == 1) {
      arg3Expr = destExprs[0];
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDX], destExprs[0]);
    }
  }
  //LOG_TASE("DBG AH1 \n");LOG_FLUSH();
  
  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) &&
       (isa<ConstantExpr>(arg3Expr))
       ){
    void * buf = (void *) target_ctx_gregs[GREG_RSI].u64;
    size_t count = (size_t) target_ctx_gregs[GREG_RDX].u64;
    if ( verTestType == VerTestType::TRAIN ) {
      if (!onValidPath) {
	LOG_TASE("Exiting from model_mavlink_write_tase from invalid path \n");LOG_FLUSH();
	exit(0);
      }
    }

    if (verTestType == VerTestType::SINGLEMSGVER || (verTestType == VerTestType::VERIFY)  || ( verTestType == VerTestType::TRAIN && onValidPath) ) {
      //LOG_TASE("DBG AH2 \n");LOG_FLUSH();
      std::vector<uint8_t> currMsg = getCurrMsgToVerifyMavlink();
      //LOG_TASE("Message in verifier's buf: \n");LOG_FLUSH();
      //printBuf(taseLog, buf, count);fflush(taseLog);
      //LOG_TASE("Message in log: \n");LOG_FLUSH();
      //printBuf(taseLog, (void *) &currMsg[0] , count);fflush(taseLog);
      if (currMsg.size() != count) {
	LOG_TASE("cost dbg: model_write fail time %lf for  msgCtr %d \n", util::getWallTime() - T0, msgCtr);
	printGetNPossibleValuesCache();
	LOG_TASE("Worker %d reached dead end on msg %d; verifier produced length %d and found %ld in log \n", getpid(), getCurrMsgIdxMavlink(), count, currMsg.size()); LOG_FLUSH();
	fflush(stdout);
	exit(0);
      } else {
	LOG_TASE("Worker %d produced correct length message %ld \n", getpid(), count); LOG_FLUSH();
      }
      //Produce the write condition
      klee::ref<klee::Expr> write_condition = klee::ConstantExpr::alloc(1, klee::Expr::Bool);
      uint8_t * itrPtr = (uint8_t *) buf;
      for (int i = 0; i < count; i++) {
	//outs() << "Printing byte "  << i << "\n";
	ref<Expr> bufByte = tase_helper_read((uint64_t) itrPtr + i, 1);
	MOD_TASE("Buf byte %i: %s \n",i, bufByte->dumpToStr().c_str());LOG_FLUSH();

	ref<Expr> logByte = klee::ConstantExpr::alloc(currMsg[i], klee::Expr::Int8);
	//logByte->dumpToStdout();
	//outs().flush();
	ref<Expr> byteEquals = klee::EqExpr::create(tase_helper_read((uint64_t) itrPtr + i, 1),
						   klee::ConstantExpr::alloc(currMsg[i], klee::Expr::Int8));
	write_condition = klee::AndExpr::create(write_condition, byteEquals);
      }
      if (klee::ConstantExpr *CE = dyn_cast<klee::ConstantExpr>(write_condition)) {
	if (CE->isFalse()) {
	  LOG_TASE("Worker %d found false write condition for msg %d \n", getpid(), getCurrMsgIdxMavlink()); LOG_FLUSH();
	  exit(0);
	}
      }
      
      std::vector<const klee::Array*> arrays;
      double tmp2 = util::getWallTime();
      klee::findSymbolicObjects(write_condition, arrays);
      LOG_TASE("DBG2 time: %lf \n", util::getWallTime() - tmp2 ); LOG_FLUSH();
      double tmp3 = util::getWallTime();
      //klee::ConstraintManager cm (GlobalExecutionStatePtr->constraints);  //Fast

      //New
      addConstraint(*GlobalExecutionStatePtr, write_condition);

      std::vector<ref<Expr>> deps;
      if (TASEKillConsAfterVer ) {
	deps = GlobalExecutionStatePtr->constraints.getConstraintVector();
      } else {
	deps = getDepCons(write_condition, false);
      }
      LOG_TASE("deps is size %d \n", deps.size());LOG_FLUSH();
      for (int i = 0; i < deps.size(); i++) {
	MOD_TASE("EXPR %d: %s \n",i, deps[i]->dumpToStr().c_str());LOG_FLUSH();
      }
      klee::ConstraintManager cm (deps);
      LOG_TASE("DBG3 time: %lf \n", util::getWallTime() - tmp3 ); LOG_FLUSH();
      double tmp4 = util::getWallTime();
      //cm.addConstraint(write_condition, &arrays); //New -- removed
      LOG_TASE("DBG4 time: %lf \n", util::getWallTime() - tmp4 ); LOG_FLUSH();
      double tmp5 = util::getWallTime();
      klee::Query query(cm, klee::ConstantExpr::alloc(0, klee::Expr::Bool));
      LOG_TASE("DBG5 time: %lf \n", util::getWallTime() - tmp5 ); LOG_FLUSH();
      double tmp6 = util::getWallTime();
      std::vector< std::vector<unsigned char> > initial_values;
      bool res = solver->solver->getInitialValues(query, arrays, initial_values);
      LOG_TASE("DBG6 time: %lf \n", util::getWallTime() - tmp6 ); LOG_FLUSH();
      if (res) {
	LOG_TASE("Worker %d successfully verified msg %d \n", getpid(), getCurrMsgIdxMavlink());LOG_FLUSH();
	
	void * logMsgBuf = (void *) &currMsg[0];
	//This is actually inteded for singleMsgVer, since we run it to get clusters
	//and THEN we do training using the cluster info as a trace.
	clusterEndType = "SEND";
	if (verTestType == VerTestType::SINGLEMSGVER ) {
	  resetAndWriteCluster(logMsgBuf, currMsg.size(), "mavlinkClusters");
	}
	msgCtr++;
	resetBranches();
	currMsgVerIdx++;
	clearExecutionFragment();
	branchesSinceLastMsg = 0;
	double tmp1 = util::getWallTime();
	//Added BFS to printGetNPossibleValuesCache because our BFS exploration for pretraining needs to be fast
	if (msgCtr == msgsToVerify || explorationType == TASEExplorationType::BFS) {
	  printGetNPossibleValuesCache(); //TODO: Gate this logic so it's available for testing
	}
	LOG_TASE("getNPossibleValuesCache print time %lf \n", util::getWallTime() - tmp1);LOG_FLUSH();
	workerResetFeats();
	LOG_TASE("DBG1 Time: %lf seconds for msgCtr %d \n", util::getWallTime() - T0, msgCtr -1);LOG_FLUSH();
	LOG_TASE("cost dbg: model_write time %lf for  msgCtr %d \n", util::getWallTime() - T0, msgCtr -1);  LOG_FLUSH();  
	worker_success(Stopped, Running);
	if (verTestType == VerTestType::SINGLEMSGVER  || ( verTestType == VerTestType::TRAIN && onValidPath) ) {
	  exit(0);
	} else {
	  //LOG_TASE("Successful worker %d stopping self and waiting for manager \n", getpid());LOG_FLUSH();
	  //kill(getpid(), SIGSTOP); //Stop self and wait for manager to kill dead ends from current round
	  //workerResetFeats();
	  //workerPrepForReplay();
	  
	  LOG_TASE("Successful worker %d running again \n", getpid());LOG_FLUSH();
	}
	
      } else {
	//printf("Worker %d failed to find solution for write condition for msg %d \n", getpid(), (int)  singleMsgVerificationIdx);fflush(stdout);
	LOG_TASE("cost dbg: model_write fail time %lf for  msgCtr %d \n", util::getWallTime() - T0, msgCtr);
	printGetNPossibleValuesCache();
	LOG_TASE("Worker %d failed to find solution for write condition for msg %d \n", getpid(), (int)  singleMsgVerificationIdx);LOG_FLUSH();	
	exit(0);
      }      
    } else {
      LOG_TASE("ERROR: Unhandled vertesttype in model_mavlink_write_tase \n"); LOG_FLUSH();
      exit(1);
    }
    calleeKillDeadRegs();
    
    reset_round_constraint_features();
    if (TASEKillConsAfterVer) {
      GlobalExecutionStatePtr->constraints.clear();
    }
    do_ret();
  } else {
    //printf("ERROR in model_mavlink_write_tase - symbolic arg \n");
    //std::cout.flush();
    LOG_TASE("ERROR in model_mavlink_write_tase - symbolic arg \n");
    LOG_FLUSH();
    std::exit(EXIT_FAILURE);
  }

  
}
void peekChannelState (void *state);
//This model is here so we can verify an individual message without verifying all the
//messages before it.  It basically just updates the message counter as if we had sent
//N-1 messages before attempting to send message N.  The message counter is transmitted as
//a part of the message.
bool inModelPCS = false;
void Executor::model_peek_channel_state() {
  inModelPCS = true;
  static int callCtr = 0;
  LOG_TASE("Entering model_peek_channel_state for time %d \n", callCtr); LOG_FLUSH();
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  if  (
       (isa<ConstantExpr>(arg1Expr))
       ){
    mavlink_status_t * statePtr = (mavlink_status_t *) target_ctx_gregs[GREG_RDI].u64;
    if (verTestType == VerTestType::SINGLEMSGVER || verTestType == VerTestType::TRAIN) {
      statePtr->current_tx_seq = singleMsgVerificationIdx % 256;
      LOG_TASE("current_tx_seq is now %d \n", statePtr->current_tx_seq);
    } else if (verTestType == VerTestType::VERIFY) {
      //Only need to set the sequence counter once for full verification.  It will update after that
      //automatically
      if (callCtr == 0) {
	statePtr->current_tx_seq = singleMsgVerificationIdx % 256;
	LOG_TASE("current_tx_seq is now %d \n", statePtr->current_tx_seq);
      }
    }
    uint8_t * itrPtr = (uint8_t *) statePtr;
    double T0 = util::getWallTime();
    //Maybe batch this up?
    //LOG_TASE("Printing channel state bytes at 0x%lx \n", (uint64_t) statePtr);LOG_FLUSH();
    for (int i = 0; i < sizeof(mavlink_status_t); i++) {
      ref<Expr> bufByte = tase_helper_read((uint64_t) (itrPtr + i), 1);
      MOD_TASE("Buf byte %i: %s \n",i, bufByte->dumpToStr().c_str());LOG_FLUSH();
      if (!isa<ConstantExpr> (bufByte) ) {
	LOG_TASE("Symbolic byte in channel state \n");LOG_FLUSH();
	ExecutionState dummy = ExecutionState(getDepCons(bufByte, false));
	
	LOG_TASE("Dummy has %d constraints \n", dummy.constraints.getConstraintVector().size());
	std::vector<ref<Expr>> realCons = GlobalExecutionStatePtr->constraints.getConstraintVector();
	LOG_TASE("Real ES has %d constraints \n", realCons.size());
	/*
	for (int i = 0; i < realCons.size(); i++) {
	  LOG_TASE("Real con %d: %s \n", i, realCons[i]->dumpToStr().c_str());LOG_FLUSH();
	  }*/
	
	//LOG_FLUSH();
	//LOG_TASE("model_peek_channel_state calling getNPossibleValues \n");LOG_FLUSH();
	std::vector<ref<Expr>> vals  = getNPossibleValues(dummy, bufByte, 10);
	//LOG_TASE("model_peek_channel_state called getNPossibleValues \n");LOG_FLUSH();
	//std::vector<ref<Expr>> vals  = getNPossibleValues(*GlobalExecutionStatePtr, bufByte, 10); orig
	if (vals.size()  == 1) {
	  LOG_TASE("Trivial concretization of state byte %d \n", i); LOG_FLUSH();
	  tase_helper_write((uint64_t) (itrPtr + i), vals[0]);
	} else {
	  LOG_TASE("More than 1 val \n");LOG_FLUSH();
	}
      }
      //LOG_TASE("DBG 12345 \n");LOG_FLUSH();
    }
    LOG_TASE("%lf seconds spend in peek_channel_state \n", util::getWallTime() - T0);LOG_FLUSH();
    LOG_TASE("Leaving model_peek_channel_state for time %d \n", callCtr); LOG_FLUSH();
    calleeKillDeadRegs();
    LOG_TASE("cost dbg: model_peek_channel_state time %lf for  msgCtr %d \n", util::getWallTime() - T0, msgCtr);  LOG_FLUSH();
    callCtr++;
    do_ret();

    inModelPCS = false;
  } else {
    printf("ERROR in model_peek_channel_state - symbolic arg \n");
    std::cout.flush();
    std::exit(EXIT_FAILURE);
  }
}

void Executor::forkOnPossibleRIPValuesMavlink(ref <Expr> inputExpr, uint64_t initRIP) {
  static int callCtr = 0;
  LOG_TASE("Entering forkOnPossibleRIPValuesMavlink for time %d \n", callCtr);
  callCtr++;
  branchType = 0;
  //preBranchBB = initRIP;
  //Determine if inputExpr actually has a solution given current path constraints.  Don't use
  //cheat info (e.g., keystrokes), hence the "false".

  DBG_TASE("Attempting to call toUniquePreCalc \n");fflush(stdout);
  /*
    outs() << "Printing  expr \n";
    inputExpr->dumpToStdout();
    outs() << "Printed exp \n";
    outs().flush();
  */
  double T0 = util::getWallTime();
  ExecutionState e(getDepCons(inputExpr,false));
  std::vector<ref<Expr>> vals = getNPossibleValues(e,inputExpr, 100);
  if (vals.size() == 1) {
    LOG_TASE("Only one valid value for RIP \n");LOG_FLUSH();
    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], vals[0]);
    return;
  }/*
  inputExpr = toUniquePreCalc(inputExpr, false);
  LOG_TASE("Returned from toUniquePreCalc inForkOnPossibleRIPVals in %lf seconds \n", util::getWallTime() - T0);
  if (isa<ConstantExpr> (inputExpr)) {
    LOG_TASE("Only one valid value for RIP \n");LOG_FLUSH();
    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], inputExpr);
    return;
    }*/

  branchDepth++;
  if (!inForkElisionReplay) { //Replayed worker already has correct number of branches from slot
    addBranch();
  }
  branchesSinceLastMsg++;
  
  if (verTestType == VerTestType::REPLAY ) {
    //Replay case -- We shouldn't be here because nothing is symbolic during a replay
    printf("ERROR: Entered forkOnPossibleRIPValues during concrete replay test \n");fflush(stdout);
    exit(0);
  } else if (verTestType == VerTestType::TRAIN ) {
    mavlinkTrainingFork(inputExpr, initRIP);
  } else if (verTestType == VerTestType::SINGLEMSGVER || (verTestType == VerTestType::VERIFY)) {
    LOG_TASE("Multiple branches detected in forkOnPossibleRIPValuesMavlink \n");LOG_FLUSH();
    std::vector<ref<Expr>> deps = getDepCons(inputExpr,false);
    LOG_TASE("Deps has size %d \n", deps.size()); LOG_FLUSH();
    ExecutionState dummy = ExecutionState(deps);
    std::vector<ref<Expr>> destExprs = getNPossibleValues(dummy, inputExpr, 100);
    //std::vector<ref<Expr>> destExprs = getNPossibleValues(*GlobalExecutionStatePtr, inputExpr, 100);
    std::vector<uint64_t> dests;
    for (int i = 0; i < destExprs.size() ; i++) {
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(destExprs[i])) {
	dests.push_back(CE->getZExtValue());
      } else {
	printf("Something went wrong in getNPossibleValues \n");
	exit(0);
      }
    }
    DBG_TASE("Found %d dests \n", dests.size());
    for (int i = 0; i < dests.size(); i++) {
      DBG_TASE("0x%lx \n", dests[i]);
    }
    //int branchIdx= tase_fork(getpid(), initRIP, dests);

    //addConstraint(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, destExprs[branchIdx]));
    //target_ctx_gregs_OS->write(GREG_RIP*8, destExprs[branchIdx]);
    printf("Calling tase_fork_RIP \n");fflush(stdout);
    printGetNPossibleValuesCache();

    std::vector<std::vector<float>> RIP_Constraint_BOWs;
    if (klee::useLEARCHFeatsOracle) {
      RIP_Constraint_BOWs = getRIPConstraintBOWs(inputExpr, destExprs);
    }
    int branchIdx= tase_fork_RIP(dests, RIP_Constraint_BOWs);  
    addConstraint(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, destExprs[branchIdx]));
    loadGetNPossibleValuesCache();
    ConstantExpr * CE = dyn_cast<ConstantExpr> (destExprs[branchIdx]);
    uint64_t IP = CE->getZExtValue();
    execution_fragment.push_back(getMLBBID(IP));
    target_ctx_gregs_OS->write(GREG_RIP*8, destExprs[branchIdx]);
    //Pick up here
  } else {
    printf("ERROR: Fell through bottom case in forkOnPossibleRIPValues \n");fflush(stdout);
    exit(0);
  }
}
extern std::vector<double> round_constraint_features;

std::vector<std::vector<float>> Executor::getRIPConstraintBOWs(ref<Expr> inputExpr,  std::vector<ref<Expr>> destExprs) {
  std::vector<std::vector<float>> res;
  
  for (int i = 0; i < destExprs.size(); i++) {
    //float currBOW[32];
    std::vector<float> currBOW;
    addConstraintFeature(EqExpr::create(inputExpr, destExprs[i]));

    for (int j= 0; j < 32; j++) {
      //currBOW[j] = round_constraint_features[j];
      currBOW.push_back(round_constraint_features[j]);
    }
    res.push_back(currBOW);
    remConstraintFeature(EqExpr::create(inputExpr, destExprs[i]));
  }

  return res;
}

int currMavlinkTrainingBBIdx = 0;

uint64_t getCurrMavlinkTrainingBBID() {
  if (currMavlinkTrainingBBIdx >=  loadedMavlinkTrainingBBIDs.size()) {
    printf("ERROR: idx %d out of bounds for training BBIDs \n", currMavlinkTrainingBBIDIdx);fflush(stdout);
  }
  uint64_t res = loadedMavlinkTrainingBBIDs[currMavlinkTrainingBBIDIdx];
  currMavlinkTrainingBBIDIdx++;
  return res;
}

void Executor::mavlinkTrainingFork(ref <Expr> inputExpr, uint64_t initRIP) {
  static int callCtr = 0;
  uint64_t goodMLBBID = 0;
  
  if (onValidPath) {
    printf("Entering mavlinkTrainingFork for time %d on valid path\n", callCtr);fflush(stdout);
    callCtr++;
  } 
  if (trainType == TASETrainType::ML ) {
    if (onValidPath) {
      printf("PID %d entering mavlinkTrainingFork on valid path \n",getpid());fflush(stdout);
    } else {
      printf("PID %d entering mavlinkTrainingFork on invalid path \n", getpid());fflush(stdout);
    }
    
    ExecutionState dummy = ExecutionState(getDepCons(inputExpr, false));
    std::vector<ref<Expr>> rips = getNPossibleValues (dummy, inputExpr, 100);
    printf("Found %d possible symbolic RIP values \n", rips.size());fflush(stdout);
    printNPossibleValues(*GlobalExecutionStatePtr, inputExpr, 100);    
    
    ref<Expr> uniqueRIPExpr;
    if (onValidPath) {
      uint64_t validBBID = getCurrMavlinkTrainingBBID();
      printf("ValidBBID appears to be %ld \n", validBBID);fflush(stdout);
      //Check to make sure valid BBID is one of the destinations
      bool foundMatch = false;
      for (int i = 0; i < rips.size(); i++) {
	ConstantExpr * CE = dyn_cast<ConstantExpr> (rips[i]);
	uint64_t IP = CE->getZExtValue();
	printf("IP is 0xlx \n", IP);fflush(stdout);
	uint64_t ID = getMLBBID(IP);
	printf("Found BBID %ld \n", ID);fflush(stdout);
	if (ID == validBBID) {
	  printf("MATCH  on ID %ld \n", ID); fflush(stdout);
	  goodMLBBID = ID;
	  uniqueRIPExpr = rips[i];
	  foundMatch = true;
	}
      }
      if (!foundMatch) {
	printf("ERROR: Could not find traced RIP in list of RIPs in training fork \n");
	
	fflush(stdout);
	exit(0);
      }

    }
    
    for (int i = 0; i < rips.size(); i++) {
      ref<Expr> badBranchRIP;
      if (onValidPath) {
	if (uniqueRIPExpr.compare(rips[i]) == 0) {
	  printf("Good path hit continue \n");fflush(stdout);
	  continue;
	}
      }
      badBranchRIP = rips[i];
      printf("PID %d trying to fork off worker \n", getpid());
      fflush(stdout);

      int kidPid = ::fork();
      if (kidPid ==0)  {
	double kidPidStartTime = util::getWallTime();
	onValidPath = false;
	badBranchDepth++;
	ref<Expr> cons = EqExpr::create(inputExpr, badBranchRIP);
	addConstraint(*GlobalExecutionStatePtr, cons);//new
	addConstraintFeature(cons);
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], badBranchRIP);
	int currID = getNewMLID();
	ConstantExpr * CE_badBranchRIP = dyn_cast<ConstantExpr> (badBranchRIP);
	uint64_t IP_Val = CE_badBranchRIP->getZExtValue();
	dumpFeaturesMavlink(onValidPath,  currID, getMLBBID(IP_Val));
	
	if (badBranchDepth == maxBadBranchDepth) {
	  printf("PID %d exiting after time %lf \n", getpid(), util::getWallTime() - kidPidStartTime);
	  fflush(stdout);
	  std::exit(EXIT_SUCCESS);
	} else{
	  return; //Continue exploration
	}
      } else {
	int status;
	int res = waitpid(kidPid, &status, WUNTRACED);	  
      } 
    }
    if (onValidPath == false) {
      printf("PID %d exiting after forking off children \n", getpid());
      fflush(stdout);
      std::exit(EXIT_SUCCESS);

    }
    
    ref<Expr> cons = EqExpr::create(inputExpr, uniqueRIPExpr);

    addConstraint(*GlobalExecutionStatePtr, cons);//new
    addConstraintFeature(cons);
    cons->dumpToStdout();

    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], uniqueRIPExpr);
    int currID = getNewMLID();
    ConstantExpr * CE_badBranchRIP = dyn_cast<ConstantExpr> (uniqueRIPExpr);
    uint64_t IP_Val = CE_badBranchRIP->getZExtValue();
    dumpFeaturesMavlink(onValidPath, currID, getMLBBID(IP_Val));

    if (onValidPath) {
      printf("Leaving training fork on valid path for time %d on ID %ld with RIP 0x%lx \n", callCtr-1, goodMLBBID, target_ctx_gregs[GREG_RIP].u64);fflush(stdout);
    }
  	
  } else if (trainType == TASETrainType::CLUSTER) {

    //Figure out valid dest using cheat info and "steer" towards that BB
    ref <Expr> uniqueRIPExpr;
    double T0 = util::getWallTime() ;
    uniqueRIPExpr = toUniquePreCalc(inputExpr, true);
    LOG_TASE("Spent %lf  seconds on toUniquePreCalc with cheat \n", util::getWallTime() - T0);fflush(stdout);
    if  (!isa<ConstantExpr> (uniqueRIPExpr)) {
      printf("ERROR: RIP should be concrete after using cheat constraints \n");fflush(stdout);
      std::exit(EXIT_FAILURE);

    }
    ref<Expr> cons = EqExpr::create(inputExpr, uniqueRIPExpr);
    printf("Calling addConstraint from mavlinkTrainingFork \n");fflush(stdout);
    T0 = util::getWallTime();
    addConstraint(*GlobalExecutionStatePtr, cons);
    printf("Spent %lf  seconds on addConstraint \n", util::getWallTime() - T0);fflush(stdout);
    addConstraintFeature(cons);
    ConstantExpr * CE = dyn_cast<ConstantExpr> (uniqueRIPExpr);
    uint64_t IP = CE->getZExtValue();
    execution_fragment.push_back(getMLBBID(IP));
    //BBClusterVec.push_back(IP);
    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], uniqueRIPExpr);
  } else {
    printf("Unrecognized trainType \n");fflush(stdout);
    std::exit(EXIT_FAILURE);
  }
  
}

int Executor::forkOnPossibleIRBranchesMavlink( ref<Expr> condition, std::vector<std::vector<float>> IR_Constraint_BOWs) {
  branchType = 1;
  printf("Entering forkOnPossibleIRBranches \n");fflush(stdout);
  LOG_TASE("Entering forkOnPossibleIRBranches \n");
  /*
  if (taseDebug) {
    outs().flush();
    outs() << "Condition is \n";
    condition->dumpToStdout();
    outs().flush();
  }
  */
  double uniqueTime = util::getWallTime();
  condition =  toUniquePreCalc(condition, false);
  LOG_TASE("%lf seconds elapsed in toUniquePreCalc without cheat \n", util::getWallTime() -uniqueTime);fflush(stdout);

  if (isa<ConstantExpr> (condition)) {
    //We shouldn't ever reach this line of code because of the solver call in Executor::fork

    LOG_TASE("Sanity check failed in forkOnPossibleIRBranches \n");fflush(stdout);
    std::exit(EXIT_FAILURE);
    return 0;
  }

  branchDepth++;
  if (!inForkElisionReplay) { //Replayed worker already has correct number of branches from slot
    addBranch();
  }
  branchesSinceLastMsg++;
  
  if (verTestType == VerTestType::REPLAY) {
    //Replay case -- We shouldn't be here because nothing is symbolic during a replay
    LOG_TASE("ERROR: Entered forkOnPossibleIRBranches during concrete replay test \n");fflush(stdout);
    exit(0);
    return 0;
  } else if (verTestType == VerTestType::TRAIN) {
    LOG_TASE("Calling mavlinkTrainingIRFork \n");fflush(stdout);
    return mavlinkTrainingIRFork(condition);
  } else if (verTestType == VerTestType::SINGLEMSGVER || (verTestType == VerTestType::VERIFY)) {
    LOG_TASE("Branching on symbolic data within IR Function \n");fflush(stdout);
    uint64_t trueBranchID  = getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true ));
    uint64_t falseBranchID = getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false));
    printGetNPossibleValuesCache();
    int isTrueChild = tase_fork_IR(trueBranchID, falseBranchID, IR_Constraint_BOWs);
    if (isTrueChild == 1) {
      execution_fragment.push_back(trueBranchID);
    } else {
      execution_fragment.push_back(falseBranchID);
    }
    loadGetNPossibleValuesCache();
    return isTrueChild;
  } else {
    LOG_TASE("ERROR: Fell through bottom case in forkOnPossibleIRBranches \n");fflush(stdout);
    std::exit(EXIT_FAILURE);
    return -1;
  }  
}

int Executor::mavlinkTrainingIRFork(ref<Expr> condition) {
  if (trainType == TASETrainType::ML ) {
    ExecutionState dummy = ExecutionState(getDepCons(condition, false));
    std::vector<ref<Expr>> conditionVals = getNPossibleValues (dummy, condition, 100);
    LOG_TASE("Found %d possible symbolic branch condition values \n", conditionVals.size());fflush(stdout);
    if (conditionVals.size() != 2) {
      LOG_TASE("Sanity check failed in training IR fork: More than 2 condtion values %d \n", conditionVals.size());
      LOG_FLUSH();
      exit(1);
    }
    bool validPathCond;
    if (onValidPath) {
      uint64_t validTrainingBBID = getCurrMavlinkTrainingBBID();
      printf("ValidTrainingBBID appears to be %ld \n", validTrainingBBID);fflush(stdout);
      //Check to make sure valid BBID is one of the destinations
      uint64_t trueBranchID = getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true));
      uint64_t falseBranchID = getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false));
      if (validTrainingBBID == trueBranchID) {
	validPathCond = true;
      } else if (validTrainingBBID == falseBranchID) {
	validPathCond = false;
      } else {
	printf("ERROR: Unhandled case in assigning validTrainingBBID \n");fflush(stdout);
	exit(1);
      }
    }

    if (!onValidPath || (onValidPath && !validPathCond )) {
      printf("PID %d trying to fork off worker for true condition \n", getpid());
      fflush(stdout);

      //TRUE
      int trueKidPid = ::fork();
      if (trueKidPid ==0)  {
	double trueKidPidStartTime = util::getWallTime();
	onValidPath = false;
	badBranchDepth++;
	addConstraint(*GlobalExecutionStatePtr, condition);//new
	addConstraintFeature(condition);
	int currID = getNewMLID();
	dumpFeaturesMavlink(onValidPath,  currID,  getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true)));

	if (badBranchDepth == maxBadBranchDepth) {

	  printf("PID %d exiting  \n", getpid());
	  fflush(stdout);
	  std::exit(EXIT_SUCCESS);
	} else{
	  return 1; //Continue exploration
	}

      } else {
	int status;
	int res = waitpid(trueKidPid, &status, WUNTRACED);
      }
    }

    if (!onValidPath || (onValidPath && validPathCond )) {
      printf("PID %d trying to fork off worker for false condition \n", getpid());
      fflush(stdout);
    
      //FALSE
      int falseKidPid = ::fork();
      if (falseKidPid ==0)  {
	double falseKidPidStartTime = util::getWallTime();
	onValidPath = false;
	badBranchDepth++;
	addConstraint(*GlobalExecutionStatePtr, Expr::createIsZero(condition));//new
	addConstraintFeature(Expr::createIsZero(condition));
	int currID = getNewMLID();
	dumpFeaturesMavlink(onValidPath,  currID,  getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false)));

	if (badBranchDepth == maxBadBranchDepth) {
	  printf("PID %d exiting  \n", getpid());
	  fflush(stdout);
	  std::exit(EXIT_SUCCESS);
	} else{
	  return 0; //Continue exploration
	}

      } else {
	int status;
	int res = waitpid(falseKidPid, &status, WUNTRACED);
      }
    }    
    if (onValidPath == false) {
      printf("PID %d exiting after forking off children  \n", getpid());
      fflush(stdout);
      std::exit(EXIT_SUCCESS);
    }

    if (validPathCond) {
      addConstraint(*GlobalExecutionStatePtr,condition);
      addConstraintFeature(condition);
      int currID = getNewMLID();
      dumpFeaturesMavlink(onValidPath, currID,getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true)));

      return 1;
    } else {
      addConstraint(*GlobalExecutionStatePtr,Expr::createIsZero(condition));
      addConstraintFeature(Expr::createIsZero(condition));
      int currID = getNewMLID();
      dumpFeaturesMavlink(onValidPath, currID,getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false)));

      return 0;      
    }    
  } else if (trainType == TASETrainType::CLUSTER ) {
    ref <Expr> uniqueConditionVal;
    double T0 = util::getWallTime() ;
    uniqueConditionVal = toUniquePreCalc(condition, true);
    printf("%lf seconds elapsed in toUniquePreCalc with cheat \n", util::getWallTime() - T0);fflush(stdout);
    if  (!isa<ConstantExpr> (uniqueConditionVal)) {
      printf("ERROR: Branch condition should be concrete after using cheat constraints \n");fflush(stdout);
      std::exit(EXIT_FAILURE);
    }

    if (ConstantExpr * CE = dyn_cast<ConstantExpr> (uniqueConditionVal)) {
      uint64_t conditionValue = CE->getZExtValue();
      printf("conditionValue is %lu \n", conditionValue);fflush(stdout);
      if (conditionValue == 1) {
	execution_fragment.push_back(getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true )));
	return 1;
      } else if (conditionValue == 0) {
	execution_fragment.push_back(getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false)));
	return 0;
      } else {
	printf("ERROR:Unexpected condition value %llu \n", conditionValue);
	fflush(stdout);
	exit(0);
	return -1;
      }

    } else {
      printf("ERROR: Condition value not constant expr \n");
      fflush(stdout);
      exit(0);
      return -1;
    }
  }
}

std::vector<uint64_t> loadMavlinkTrainingCluster() {
  std::string clusterBaseName = "mavlinkClusters";
  //LOG_TASE("DBG2: Definitely in loadMavlinkTrainingCluster with idx %d \n", msgIdx);
  //Todo -- figure out why msgIdx is 0 despite being passed...Something weird is going on.
  //LOG_TASE(" klee arg is %d \n", (int) klee::singleMsgVerificationIdx);
  std::string clusterName = clusterBaseName + std::to_string((int) klee::singleMsgVerificationIdx);

  LOG_TASE("Attempting to load file with name %s \n", clusterName.c_str()); LOG_FLUSH();
  FILE * tmpFile = fopen(clusterName.c_str(), "r");
  if (tmpFile == NULL) {
    perror("tmpFile: ");
  } else {
    LOG_TASE("Opened file %s successfully\n", clusterName.c_str());
  }
  
  std::vector<uint64_t> branches;
  
  //Skip first 2 lines to get the branches on line 3
  for (int i = 0; i < 2; i++) {
    int c = fgetc(tmpFile);
    while( c != '\n') {
      c = fgetc(tmpFile);
    }
  }
  
  //Todo -- find a cleaner way to handle getting the line without assuming a max length
  char line [10000];
  fgets(line, 10000, tmpFile);
  DBG_TASE("Read line %s \n", line);fflush(stdout);
  char * tok = strtok(line, ",");
  while (tok != NULL) {
    uint64_t currBBID = 0;
    DBG_TASE("Found tok %s \n", tok);fflush(stdout);
    sscanf(tok, "%lu", &currBBID);
    DBG_TASE("Scanned in as 0x%lu \n", currBBID);fflush(stdout);
    tok = strtok(NULL, ",");
    if (currBBID != 0) {
      branches.push_back(currBBID);
    } else {
      DBG_TASE("Empty token \n"); //Todo -- Find a better way to handle when tok is the newline
    }
  }
  
  DBG_TASE("Found %d branch IDs \n", branches.size());fflush(stdout);
  LOG_TASE("DBG1 \n");LOG_FLUSH();
  loadedMavlinkTrainingBBIDs = branches;
  LOG_TASE("DBG2 \n");LOG_FLUSH();
  return branches;
  
}


std::vector<uint8_t> getCurrMsgToVerifyMavlink() {
  std::vector<uint8_t> res;
  if (verTestType == VerTestType::SINGLEMSGVER ) {
    res = mavlinkMsgs[singleMsgVerificationIdx];
  } else if (verTestType == VerTestType::VERIFY) {
    res = mavlinkMsgs[currMsgVerIdx];
  } else if (verTestType == VerTestType::TRAIN) {
    return mavlinkMsgs[msgCtr]; //Todo - fix dependence on msgCtr for different versions
  } else {
    LOG_TASE("ERROR: Unhandled case in getCurrMsgToVerify\n"); LOG_FLUSH();
    exit(0);
  }
  return res;
}

int getCurrMsgIdxMavlink() {
  if (verTestType == VerTestType::SINGLEMSGVER || verTestType == VerTestType::TRAIN ) {
    return singleMsgVerificationIdx;
  } else if (verTestType == VerTestType::VERIFY) {
    return currMsgVerIdx;
  } else if (verTestType == VerTestType::TRAIN) {
    return msgCtr;
  } else {
    LOG_TASE("ERROR: Unhandled case in getCurrMsgIdxMavlink\n"); LOG_FLUSH();
    exit(0);
    return -1;
  }
}

double getMavlinkArrTime(int i ) {
  return mavlinkMsgTimes[i];
}

double getCurrMsgArrTimeMavlink() {
  int i = getCurrMsgIdxMavlink();
  return getMavlinkArrTime(i);
}

uint64_t getMavlinkMsgType(int i ) {
  std::vector<uint8_t> msg = mavlinkMsgs[i];

  //Version 1 case:
  if (msg[0] == 0xfe) {
    return msg[5];
  } else if (msg[0] == 0xfd) { //Version 2
    uint64_t res = 0;
    //Deal with endianess; note that bytes for msg id are in 7/8/9 positions
    res |=  ((uint64_t) (msg[9] << 16));
    res |=  ((uint64_t) (msg[8] << 8));
    res |=  ((uint64_t) (msg[7]));
    return res;
  } else {
    printf("ERROR: Unhandled mavlink version in getCurrMsgTypeMavlink \n");fflush(stdout);
    exit(0);
    return 0;
  }
  
}

uint64_t getCurrMsgTypeMavlink() {
  int i = getCurrMsgIdxMavlink();
  return getMavlinkMsgType(i);
}
 
uint64_t getCurrMsgLenMavlink() {
  std::vector<uint8_t> currMsg = getCurrMsgToVerifyMavlink();
  return currMsg.size();
}



//int mavlinkFeatPadLen = 69;
  void Executor::dumpFeaturesMavlink(bool isValidState,  int ID, uint64_t MLBBID) {
   int numFeatsPrinted = 0;
   LOG_TASE("Writing features with isValidState %d \n", (int) isValidState);LOG_FLUSH();
   std::string logName;
   logName = "FeatureLog.txt";

   if (featLog == NULL) {
     featLog = fopen(logName.c_str(), "a+");
   }

//   if (int(isValidState) == 1 && makeInitialBranchMap) {
//     printf("ERROR: merge in iterative LSTM training logic \n");fflush(stdout);
//     exit(0);
//     printf("Updating message branch map with %d %d \n", msgCtr, mlInfo.branchesSinceLastMsg);fflush(stdout);

//     //updateMessageBranchMap(&initialMessageBranchMap,msgCtr, branchesSinceLastMsg);
//   }

   fprintf(featLog, "%d,", int(isValidState)); numFeatsPrinted++; //0
   fprintf(featLog, "%d,", ID);  numFeatsPrinted++;  //1
   fprintf(featLog, "%d,", MLParentID);  numFeatsPrinted++; //2
   fprintf(featLog, "%d,", (int) mavlinkTraceNum); numFeatsPrinted++; //3
   fprintf(featLog, "%d,", msgCtr); numFeatsPrinted++; //4
   fprintf(featLog, "%d,", getMLBBID(pre_interp_RIP)); numFeatsPrinted++; //5
   fprintf(featLog, "%d,", MLBBID); numFeatsPrinted++;  //6
//   printf("Mapping RIP 0x%lx to MLBBID %ld \n", target_ctx_gregs[GREG_RIP].u64, getMLBBID(target_ctx_gregs[GREG_RIP].u64)); fflush(stdout);
   fprintf(featLog, "%d,", branchDepth); numFeatsPrinted++; //7
   fprintf(featLog, "%d,", branchesSinceLastMsg); numFeatsPrinted++; //8
   fprintf(featLog, "%d,", branchType);  numFeatsPrinted++; //9
   fprintf(featLog, "%d,", last_IR_branch_type); numFeatsPrinted++; //10
   int isTerminalBranch = 0;
   if (badBranchDepth == maxBadBranchDepth) {
     isTerminalBranch =1;
   }
   fprintf(featLog, "%d,", isTerminalBranch); numFeatsPrinted++; //11

// #ifdef TASE_MAVLINK
   fprintf(featLog, "%ld,", getCurrMsgTypeMavlink()); numFeatsPrinted++; //12

   std::vector<uint8_t> currMsg = getCurrMsgToVerifyMavlink();
   fprintf(featLog, "%ld,", currMsg.size()); numFeatsPrinted++;   //13
   int numMsgBytesPrinted = 0;
   if (mavlinkMLMsgPadLen < 0) {
     LOG_TASE("ERROR: mavlinkMLMsgPadLen undefined \n"); LOG_FLUSH();
     exit(0);  //Todo -- signal an error and stop everything
   }
   for (int i = 0; i <currMsg.size();i++) {
     fprintf(featLog,"%d,", currMsg[i]);
     numFeatsPrinted++; numMsgBytesPrinted++;
   }
   while (numMsgBytesPrinted < mavlinkMLMsgPadLen) {
     fprintf(featLog,"0,"); numFeatsPrinted++; numMsgBytesPrinted++;
   }
   LOG_TASE("numFeatsPrinted is %d \n", numFeatsPrinted);LOG_FLUSH();

   if (useConstraintBOW) {
     for (int i =0; i < constraint_features.size(); i++) {
       fprintf(featLog, "%lf,", constraint_features[i]);
     }
     for (int i =0; i < round_constraint_features.size(); i++) {
       fprintf(featLog, "%lf,", round_constraint_features[i]);
     }
   }

   if (useBBBOW) {
     for (int i = 0; i < BBBowVec.size(); i++) {
       fprintf(featLog, "%d,", BBBowVec[i]);
     }
   }

   fprintf(featLog, "\n");
   fflush(featLog);
   MLParentID = ID;
   printf("Returning from dumpFeatures \n");
   fflush(stdout);

  
}
