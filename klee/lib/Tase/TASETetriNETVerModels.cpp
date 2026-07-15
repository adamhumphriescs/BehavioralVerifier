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
#include <curses.h>
#include "tase/EditDistanceOracle.h"
#include "tase/TASEConstraintBOWEncoding.h"
#include "ClientWorkerFeats.h"
#include "API.h"
FILE * cluster_log;
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
extern int branchDepth;
//extern void worker_exit(int);
//extern bool modelDebug;

//extern int stats_branches;
int branchType = -1;
int last_IR_branch_type = 0;
extern bool logBadBranch;
extern uint64_t pre_interp_RIP;
//uint64_t preBranchBB;
extern bool singleStepping;

extern uint64_t getMLBBID (uint64_t rip);
uint64_t getMLBBIDWithIR(uint64_t rip, int IRBranchIdx);
FILE * featLog;
FILE * replayFile;
int msgCtr = 0;
bool inTestBranch = false;
std::string verMsg;
std::string nextC2SMsg;
bool inPriorityTest = false;// Variable to determine if we're currently forking off a worker for the priority test
double priorityRunStart = 0.0;
bool priorityLSTMTest =true; //Get rid of me

//extern void worker_success();
int partialUpdateMsgCtr = 0;

int verMsgIdx = 0;
extern int tase_fork_IR(uint64_t trueBranchID, uint64_t falseBranchID, std::vector<std::vector<float>> IR_Constraint_BOWs);
extern int tase_fork_RIP(std::vector<uint64_t> dests, std::vector<std::vector<float>> RIP_Constraint_BOWs);
//std::string clusterStartType = "ENTRY";  //Valid Types: ENTRY, SEND or SELECT (no select in our TetriNET)
std::string clusterEndType = "NONE";  //Valid Types: SEND (removed RECV)
//std::vector<uint64_t> BBClusterVec;
void resetAndWriteCluster(void * msg, size_t msgSize, std::string clusterLogName);
std::map<int,int> initialMessageBranchMap;// Map of initial branches required per msg index
std::map<int, int> bestMessageBranchMap; // Map of best (shortest) branches required per msg index
void printMessageBranchMap(std::map<int,int> mapping, FILE * output);
void * prevLogMsgs;
int prevLogMsgsSize;
void * nextLogMsgs;
int nextLogMsgsSize;
std::vector<ref<Expr>> trainInputExprs; // Set of exprs corresponding to inputs.  We can solve for these
//to get the equivalent key inputs.  I guess we might use this info for future training.
bool onValidPath = true; //Variable used during training to indicate if we're following the path corresponding
//to the path actually executed by the client (as opposed to small deviations from it) 
int badBranchDepth = 0;  //Current number of branches we've explored away from the "validPath" during training. 
int maxBadBranchDepth = 2; //Max number of branches we're permitted to explore away from the "validPath" during training.
extern int getNewMLID();
double kidPidStartTime = 0.0;
extern std::string pathOracleFilePathArg;
extern double updateLSTMPred(int x, int y, int rot, uint64_t branchesSinceLastMsg, uint64_t BBID);
extern double peekLSTMPred (int x, int y, int rot, uint64_t branchesSinceLastMsg, uint64_t BBID);
extern "C" void workerResetFeats();
std::vector<ref<Expr>> cheatCons;
std::vector<uint64_t> execution_fragment; //duplicated with BBBOWVec
extern uint64_t branchesSinceLastMsg ;
double single_msg_test_start_time = 0;

//Cludge on 02172025 to avoid retraining models with RIP shifting
//int BB_SHIFT_CLUDGE = 1278;

//#define TASE_TETRINET

int preWriteTetriLogOff = 0;
bool prevWasLvl = false;
extern bool inForkElisionReplay;

extern int current_piece;
#ifdef TASE_TETRINET
extern int current_x;
extern int current_y;
extern int current_rotation;
//extern std::ifstream keyLog;
#endif

void setTetrinetBaseFeats();
static void draw_own_field(FILE * log);
extern int singleMessagePriorityTestTetrinet();
extern int random_seed_init;

extern UFManager *ufmanager;
extern UFManager *ufmanager_cheat;
extern "C" void clearExecutionFragment();
extern "C" void resetBranches();
extern "C" void addBranch();

namespace klee {
  extern int singleMsgVerificationIdx;
  extern bool useFallBackOracle;//Determine if we need to fall back to another oracle after a certain threshold is reached
  extern int fallBackBranchThreshold;//Fall back to the second oracle if we fail to verify in branches less than or equal to this number
  extern bool fallbackOracleActive;
  extern bool useCoordsWithoutMH;
  extern bool useLEARCHFeatsOracle;
};

int numLogRecords = 0;
size_t currTetriLogIdx = 0;
enum TetriNETMsgType_t  {
			 puC2S, sbC2S, lvlC2S, otherC2S, S2C, INPUT
};
struct TetriNETLogRecord {
  enum TetriNETMsgType_t type; 
  std::string msg;
  double timeStamp;
};

std::string next_msg_to_verify = "NONE";
std::vector<TetriNETLogRecord> tetriMsgLog;
std::vector<int> pieceIDs;
void loadTetriNETLogs(std::string fileName) {
  std::ifstream log = std::ifstream(fileName.c_str());
  if (log.peek() == std::ifstream::traits_type::eof()) {
    LOG_TASE("ERROR: File %s appears to contain no tetrinet logs \n", fileName.c_str());
    exit(0);
  }

  std::string line;
  std::getline(log, line); //Skip initial cmd
  std::getline(log, line); //Skip timestamp of initial cmd

  while (std::getline(log, line)) {
    
    struct TetriNETLogRecord currRecord;
    
    if (line.find("C2S") != std::string::npos) {
      if (line.find("p 1") != std::string::npos) {
	currRecord.type = puC2S;
      } else if (line.find("sb ") != std::string::npos) {
	currRecord.type = sbC2S;
      } else if (line.find("lvl ") != std::string::npos) {
	currRecord.type = lvlC2S;
      } else {
	currRecord.type = otherC2S;
      }
      
    } else if (line.find("S2C") != std::string::npos) {
      currRecord.type = S2C;
    } else if (line.find("INPUT") != std::string::npos) {
      currRecord.type = INPUT;
    } else {
      LOG_TASE("ERROR parsing line %s in tetrinet log: unknown record type \n", line.c_str());LOG_FLUSH();
      std::exit(EXIT_FAILURE);
    }
    currRecord.msg  = line.substr(line.find(":") + 2); //Strip off first part of log msg, e.g., "C2S MSG: "
    //We now expect a timestamp line.  Example: "0.000594 seconds"
    std::getline(log,line);
    if (line.find("seconds") == std::string::npos) {
      printf("ERROR parsing line %s in tetrinet log: expected timestamp info \n", line.c_str());fflush(stdout);
      std::exit(EXIT_FAILURE);
    }
    //First token should be the time;
    std::string timeStr = line.substr(0, line.find(" "));
    double time =  stod(timeStr);
    currRecord.timeStamp = time;
    tetriMsgLog.push_back(currRecord);
  }
}

void printTetriNETLogs() {
  printf("Printing tetrinet log info-----------------\n");fflush(stdout);
  for(unsigned int i = 0; i < tetriMsgLog.size(); i++) {
    struct TetriNETLogRecord curr = tetriMsgLog[i];
    enum TetriNETMsgType_t msgType = curr.type;
    std::string msg = curr.msg;
    double time = curr.timeStamp;
    if (msgType == puC2S) {
      printf("(%d) RECORD TYPE: partial update C2S", i);
    } else if (msgType == sbC2S) {
      printf("(%d) RECORD TYPE: special block C2S", i);
    } else if (msgType == lvlC2S) {
      printf("(%d) RECORD TYPE: level C2S", i);
    } else if (msgType == otherC2S) {
      printf("(%d) RECORD TYPE: other C2S", i);
    } else if (msgType == S2C) {
      printf("(%d) RECORD TYPE: S2C", i);
    } else if (msgType == INPUT) {
      printf("(%d) RECORD TYPE: user input", i);
    } else {
      printf("ERROR: Unknown msg type in tetrinet log \n");fflush(stdout);std::exit(EXIT_FAILURE);
    }
    printf(":VALUE: %s", msg.c_str());
    printf(":TIMESTAMP: %lf \n", time);
    fflush(stdout);
  }
}
bool TetriLogRecordIsC2S ( struct TetriNETLogRecord r);
void printTetriNETLogToFile(std::vector<TetriNETLogRecord> tlog, std::string fname) {
  if (fname == "NONE") {
    LOG_TASE("ERROR: Populate name for printing tetrinet log to file \n");LOG_FLUSH();
    exit(0);
  }
  FILE * log = fopen(fname.c_str(), "w+");
  fprintf(log, "SYNTH LOG\n"); //Dummy line where initial cmd normally goes
  fprintf(log, "0.0 seconds\n"); //Dummy timestamp
  for (int i = 0; i < tlog.size(); i++) {
    struct TetriNETLogRecord curr = tlog[i];
    enum TetriNETMsgType_t msgType = curr.type;
    std::string msg = curr.msg;
    double time = curr.timeStamp;

    if (TetriLogRecordIsC2S(curr)) {
      fprintf(log,"C2S MSG: ");
    } else if (msgType == S2C) {
      fprintf(log,"S2C MSG: ");
    } else if (msgType == INPUT) {
      fprintf(log, "INPUT: "); 
    } else {
      LOG_TASE("ERROR: Unknown msg type when printing tetrinet log to file \n");LOG_FLUSH();
    }
    fprintf(log, "%s\n", msg.c_str());
    fprintf(log, "%lf seconds\n", time);
  }
  fflush(log);
  
}

struct TetriNETLogRecord getNextTetriLogEntry() {
  static int callCtr = 0;
  //LOG_TASE("Calling getNextTetrilogEntry for time %d \n", callCtr);
  callCtr++;
  
  
  if (currTetriLogIdx >= tetriMsgLog.size()) {
    LOG_TASE("ERROR: Unable to get get log entry.  No more log entries. \n");LOG_FLUSH();
    std::exit(EXIT_FAILURE);
  }

  
  struct TetriNETLogRecord result = tetriMsgLog[currTetriLogIdx];
  enum TetriNETMsgType_t msgType = result.type;
  std::string msg = result.msg;
  double time = result.timeStamp;
  if (msgType == puC2S) {
    //LOG_TASE("(%d) RECORD TYPE: partial update C2S", currTetriLogIdx);
  } else if (msgType == sbC2S) {
    //LOG_TASE("(%d) RECORD TYPE: special block C2S", currTetriLogIdx);
  } else if (msgType == lvlC2S) {
    //LOG_TASE("(%d) RECORD TYPE: level C2S", currTetriLogIdx);
  } else if (msgType == otherC2S) {
    //LOG_TASE("(%d) RECORD TYPE: other C2S", currTetriLogIdx);
  } else if (msgType == S2C) {
    //LOG_TASE("(%d) RECORD TYPE: S2C", currTetriLogIdx);
  } else if (msgType == INPUT) {
    //LOG_TASE("(%d) RECORD TYPE: user input", currTetriLogIdx);
  } else {
    LOG_TASE("ERROR: Unknown msg type in tetrinet log \n");fflush(stdout);std::exit(EXIT_FAILURE);
  }
  //LOG_TASE(":VALUE: %s", msg.c_str());
  //LOG_TASE(":TIMESTAMP: %lf \n", time);
  //LOG_FLUSH();
  currTetriLogIdx++;
  return result;
}
struct TetriNETLogRecord getNextTetriLogNetworkMsg() {
  struct TetriNETLogRecord res = getNextTetriLogEntry();
  while (res.type != S2C && res.type != puC2S && res.type != sbC2S && res.type != lvlC2S && res.type != otherC2S) {
    res = getNextTetriLogEntry();
  }
  return res;
}



struct TetriNETLogRecord peekNextC2SPartialUpdate() {
  int origIdx = currTetriLogIdx;
  struct TetriNETLogRecord res = getNextTetriLogEntry();
  while (res.type != puC2S) {
    res = getNextTetriLogEntry();
  }
  currTetriLogIdx = origIdx;
  return res;
}
struct TetriNETLogRecord peekNthC2SPartialUpdate(int n) {
  int origIdx = currTetriLogIdx;
  struct TetriNETLogRecord result;
  for (int i = 0; i < n+1; i++) {
    result = getNextTetriLogEntry();
    if (result.type != puC2S) {
      while (result.type != puC2S) {
	result = getNextTetriLogEntry();
      }   
    }
  }
  currTetriLogIdx = origIdx;
  return result;
}
void readTetrinetBaseFeats(float * xVal , float * yVal, float * rotVal, std::string nextMsg);
float getNthTetrinetMessageX(int n) {
  struct TetriNETLogRecord r = peekNthC2SPartialUpdate(n);
  std::string rawMsg = r.msg;
  float xVal;
  float yVal;
  float rotVal;
  readTetrinetBaseFeats(&xVal , &yVal, &rotVal, rawMsg);
  return xVal;
  
}
float getNthTetrinetMessageY(int n) {
  struct TetriNETLogRecord r = peekNthC2SPartialUpdate(n);
  std::string rawMsg = r.msg;
  float xVal;
  float yVal;
  float rotVal;
  readTetrinetBaseFeats(&xVal , &yVal, &rotVal, rawMsg);
  return yVal;
}

float getNthTetrinetMessageRot(int n) {
  struct TetriNETLogRecord r = peekNthC2SPartialUpdate(n);
  std::string rawMsg = r.msg;
  float xVal;
  float yVal;
  float rotVal;
  readTetrinetBaseFeats(&xVal , &yVal, &rotVal, rawMsg);
  return rotVal;
}

float getNthTetrinetMessagePieceID(int n) {
  return (float)  pieceIDs[n];
}
std::string getNthC2SPartialUpdateAsStr(int n) {
  struct TetriNETLogRecord r = peekNthC2SPartialUpdate(n);
  std::string str = r.msg;
  LOG_TASE("getNthC2SPartialUpdateAsStr called on idx %d to return str %s \n",n, str.c_str()); LOG_FLUSH();
  return str;
}

double getNthC2SPartialUpdateTime(int n) {
  struct TetriNETLogRecord r = peekNthC2SPartialUpdate(n);
  return r.timeStamp;
}

std::vector<uint8_t> getNthC2SPartialUpdate(int n) {
  struct TetriNETLogRecord r = peekNthC2SPartialUpdate(n);
  std::string str = r.msg;
  LOG_TASE("getNthC2SPartialUpdate called on idx %d to return str %s \n",n, str.c_str());
  std::vector<uint8_t> res (str.begin(), str.end());
  return res;
  
}

std::string tetrinetGetNextPartialUpdate() {
  return peekNextC2SPartialUpdate().msg;
}

float getTetrinetMsgX() {
  std::string msg = tetrinetGetNextPartialUpdate();
  float xVal;
  float yVal;
  float rotVal;
  readTetrinetBaseFeats(&xVal , &yVal, &rotVal, msg);
  return xVal;
}

float getTetrinetMsgY() {
  std::string msg = tetrinetGetNextPartialUpdate();
  float xVal;
  float yVal;
  float rotVal;
  readTetrinetBaseFeats(&xVal , &yVal, &rotVal, msg);
  return yVal;
}

float getTetrinetMsgRot() {
  std::string msg = tetrinetGetNextPartialUpdate();
  float xVal;
  float yVal;
  float rotVal;
  readTetrinetBaseFeats(&xVal , &yVal, &rotVal, msg);
  return rotVal;
}
float getTetrinetMsgPieceID();

bool TetriLogRecordIsC2S ( struct TetriNETLogRecord r) {
  if (r.type == puC2S || r.type == sbC2S || r.type == lvlC2S || r.type == otherC2S)
    return true;
  else
    return false;
}


std::vector<float> get1HotEncoding (int val, int size) {
  if (val < 0 || val >= size) {
    printf("ERROR: Trying to get 1hot encoding of val %d in vector of size %d \n", val, size);fflush(stdout);
    std::exit(EXIT_FAILURE);
  }
  std::vector<float> enc (size, 0.0);
  enc[val] = 1.0;
  return enc;

}

//We would need to update the training python scripts as well,
//but we should be encoding "0" as "1,0,0,0,0,0,0" rather than all zeros.
std::vector<float> getPieceEncoding(int pieceID) {
  if ( pieceID < 0 || pieceID >= 7) {
    printf("ERROR: Unexpeced piece ID %d \n", pieceID); fflush(stdout);
    std::exit(EXIT_FAILURE);
  }
  if (pieceID == 0) {
    std::vector<float> enc(7, 0.0);
    return enc;
  } else
    return get1HotEncoding(pieceID, 7);

}

bool allMsgsVerified = false;
void parseTetrinetMessageHistory(std::string msg);
extern double currMsgArriveTime;
void managerUpdateTerinetMsgHistory() {
  printf("Fix managerUpdateTerinetMsgHistory after merge for ML msg history \n");fflush(stdout);
  std::exit(EXIT_FAILURE);

  /*
  printf("Manager attempting to get next c2s message \n");fflush(stdout);
  //Advance to next c2s message
  std::string line;

  while (getline(keyLog, line)) {
    if (line.find("p 1 ") != std::string::npos) {

      parseTetrinetMessageHistory(line);
      //Grab timestamp - format is "X seconds"
      std::string msgStr = line;
      getline(keyLog, line);

      //Please shoot me
      const char * constTimeCStr = line.c_str();
      char * timeCStr = (char *) malloc(strlen(constTimeCStr) +1);
      strcpy (timeCStr, constTimeCStr);

      char * timeStr = strtok(timeCStr, " ");
      double time = atof(timeStr);

      printf("time in atod appears to be %lf for msg %s \n", time, msgStr.c_str());fflush(stdout);
      currMsgArriveTime = time;
      return;
    }
  }
  printf("Manager believes we're done with verification \n");fflush(stdout);
  allMsgsVerified = true;
  */
}

//void updateTetrinetMessageHistory(float  xVal, float  yVal, float  rotVal, float  pieceVal);
//extern double firstMessageLSTMTime;


//FIX ME WITH REFACTOR
void parseTetrinetMessageHistory(std::string msg) {
  static int callCtr = 0;
  printf("Attempting to parse tetrinetMessageHistory for msg %s \n", msg.c_str());fflush(stdout);
  if (msg.find("p 1") != std::string::npos) {
    double t0 = util::getWallTime();
    float x,y,rot, currPiece;
    LOG_TASE("DBG 1 \n");LOG_FLUSH();
    currPiece = (float) current_piece;
    readTetrinetBaseFeats(&x,&y, &rot, msg);
    //updateTetrinetMessageHistory( x, y, rot, currPiece);
    double callTime = util::getWallTime()  - t0;
    printf("Spent %lf seconds updating msg history \n", util::getWallTime() - t0);fflush(stdout);

    callCtr++;
    /*
    if (callCtr == 1) {
      firstMessageLSTMTime = callTime;
    }
    */
  } else {
    printf("Not updating tetrinet message history for msg %s \n", msg.c_str());fflush(stdout);
  }
}

void tetrinetMakeSymbolicReplay(uint64_t addr, uint64_t size, char * name);

void Executor::tetrinet_make_symbolic(uint64_t addr, uint64_t size, char * name) {
  static int callCtr = 0;
  callCtr++;
  LOG_TASE("Entering tetrinet_make_symbolic for time %d \n", callCtr);LOG_FLUSH();

  switch( verTestType ) {
  case VerTestType::REPLAY:
    tetrinetMakeSymbolicReplay(addr,  size,  name);
    break;
    
  case VerTestType::TRAIN: {
    LOG_TASE("Entering training logic for tetrinet_make_symbolic \n"); 
    //This logic to bump the callCtr in order to create a unique name is probably redundant
    std::string numStr = std::to_string(callCtr);
    char  nameBuf [30];
    strcpy (nameBuf, "input_");
    strcat(nameBuf, numStr.c_str());
    
    DBG_TASE("Making symbolic var with name %s \n",  nameBuf);
    
    tase_make_symbolic_internal(addr, size, nameBuf);
    
    klee::ref<klee::Expr> cheatCon;
    struct TetriNETLogRecord logRecord =  getNextTetriLogEntry();
    
    if ( logRecord.type != INPUT ) {
      LOG_TASE("ERROR: Expect key input in train mode \n");LOG_FLUSH();
      std::exit(EXIT_FAILURE);
    }
    
    int nextKey = atoi(logRecord.msg.c_str());
    
    LOG_TASE("Adding constraint that key is %d \n", nextKey);LOG_FLUSH();
    
    klee::ref<klee::Expr> inBuf = tase_helper_read((uint64_t) addr, 4);
    cheatCon = klee::EqExpr::create(inBuf, klee::ConstantExpr::alloc(nextKey, klee::Expr::Int32));
    cheatCons.push_back(cheatCon);
    addCheatConstraint(cheatCon);
    
    if ( taseDebug > 0 ) {
      outs().flush();
      outs() << "Cheat constraint is \n";
      cheatCon->dumpToStdout();
      outs().flush();
    }
    break;
  }
  case VerTestType::SINGLEMSGVER:
    if ( inPriorityTest ) {
      
      LOG_TASE("Making input symbolic in test branch \n");LOG_FLUSH();
      tase_make_symbolic_internal(addr, size, name);
    } else {
      tetrinetMakeSymbolicReplay(addr,  size,  name);
    }
    break;
    
  case VerTestType::VERIFY:
    if (callCtr > 2 ) { //Get past the -1 init keys.  //Todo -- deal with this corner case
      LOG_TASE("Making input symbolic \n");LOG_FLUSH();
      tase_make_symbolic_internal(addr, size, name);
    } else {
      tetrinetMakeSymbolicReplay(addr,  size,  name);
    }
    break;
  default:
    LOG_TASE("ERROR: Failed to match case for vertesttype \n");
    exit(-1);
    break;
  }

}



void tetrinetMakeSymbolicReplay(uint64_t addr, uint64_t size, char * name) {
  struct TetriNETLogRecord logRecord =  getNextTetriLogEntry();
  if (logRecord.type != INPUT) {
    printf("ERROR: Expect key input in replay mode \n");fflush(stdout); std::exit(EXIT_FAILURE);
  }
  int keyVal = atoi(logRecord.msg.c_str());
  *((int *) addr) = keyVal;
  printf("Forcing key to be %d in replay \n", keyVal);fflush(stdout);

}

//int atoi(const char *str)
void Executor::model_tetri_atoi() {
  printf("Entering model_tetri_atoi\n");fflush(stdout);
  
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);

  if  (
       (isa<ConstantExpr>(arg1Expr)) 
       ){

    char * input = (char *) target_ctx_gregs[GREG_RDI].u64;
    int res = atoi(input);
    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    tase_helper_write( (uint64_t) &target_ctx_gregs[GREG_RAX].u64, resExpr);
    do_ret();

  } else {
    printf("ERROR in model_tetri_atoi - symbolic arg \n");
    std::cout.flush();
    std::exit(EXIT_FAILURE);
  }
    
}

//ssize_t ktest_write(int fd, const void *buf, size_t count)

void model_tetri_ktest_write_replay(std::string bufMsg);
void model_tetri_ktest_write_train(std::string bufMsg);
void model_tetri_ktest_write_singleMsgVerification(std::string bufMsg);
void model_tetri_ktest_write_verification(std::string bufMsg);

//ssize_t ktest_write(int fd, const void *buf, size_t count)
void Executor::model_tetri_ktest_write() {
  static int callCtr = 0;
  LOG_TASE("Entering model_tetri_ktest_write for time %d \n", callCtr); fflush(stdout);
  callCtr++;
  
  //resetBranches(); //Only reset if we have a puC2S

  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);

  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) &&
       (isa<ConstantExpr>(arg3Expr))
       ){

    //Todo -- add logic to verify these bytes are all concrete.
    void * buf = (void *) target_ctx_gregs[GREG_RSI].u64;
    char * rawInput = (char *) buf;

    size_t count = target_ctx_gregs[GREG_RDX].u64;

    size_t len = strlen((char *) buf);

    char tmp [count +1];
    memcpy ((void *) tmp, buf, count);

    tmp[count] = '\0'; //Make it a valid c string
    std::string msg(tmp);
    /*
    if (msg.find("p 1") != std::string::npos) {
      branchesSinceLastMsg = 0;
      partialUpdateMsgCtr++;
    }
    */

    if ( verTestType == VerTestType::REPLAY ) {
      model_tetri_ktest_write_replay(msg);
    } else if ( verTestType == VerTestType::TRAIN ) {
      model_tetri_ktest_write_train(msg);
    } else if ( verTestType == VerTestType::SINGLEMSGVER ) {
      model_tetri_ktest_write_singleMsgVerification(msg);
    } else if ( verTestType == VerTestType::VERIFY ) {
      model_tetri_ktest_write_verification(msg);
    } else {
      printf("ERROR: verTestType unspecified \n"); fflush(stdout); std::exit(EXIT_FAILURE);
    }
    reset_round_constraint_features();
    
    if (msg.find("p 1") != std::string::npos) {
      branchesSinceLastMsg = 0;
      partialUpdateMsgCtr++;
    }
    

    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) count, Expr::Int64);
    tase_helper_write( (uint64_t) &target_ctx_gregs[GREG_RAX].u64, resExpr);
    do_ret();

  } else {
    printf("ERROR in model_tetri_ktest_write - symbolic arg \n");
    std::cout.flush();
    std::exit(EXIT_FAILURE);
 }
}


void model_tetri_ktest_write_replay(std::string bufMsg) {
  //Just make sure that bufMsg matches the log
  printf("Entering model_tetri_ktest_write_replay \n");fflush(stdout);
  struct TetriNETLogRecord logRecord =  getNextTetriLogEntry();
  printf("Found log record \n");fflush(stdout);

  if (bufMsg.find("p 1") != std::string::npos) {
    msgCtr++;
  }
  
 if (TetriLogRecordIsC2S(logRecord) && bufMsg.compare(logRecord.msg) == 0) {
   printf("Message in ktest_write_replay matches log \n"); fflush(stdout);
 } else {
   //This is a hack to make sure the log and verifier produced roughly the same type of message.
   //Unfortunately the message string is produced by vsnprintf, and we can't fully generate the
   //strings accurately without var args modeling.
   if ((bufMsg.find("startgame") != std::string::npos && logRecord.msg.find("startgame") != std::string::npos) ||
       (bufMsg.find("lvl") != std::string::npos && logRecord.msg.find("lvl") != std::string::npos) ||
       (bufMsg.find("team") != std::string::npos && logRecord.msg.find("team") != std::string::npos) ||
       (bufMsg.find("sb ") != std::string::npos && logRecord.msg.find("sb ") != std::string::npos)

       ) {
     printf("Msg type matches: need to implement vsnprintf to fully verify numbers in string\n");fflush(stdout);
   } else {
     
     
     printf("ERROR: message in buf:%s| doesn't match message in log:%s|\n", bufMsg.c_str(), logRecord.msg.c_str());
     fflush(stdout);
     std::exit(EXIT_FAILURE);
   }
 } 
}

void model_tetri_ktest_write_train(std::string bufMsg) {
  struct TetriNETLogRecord logRecord =  getNextTetriLogEntry();
  if (TetriLogRecordIsC2S(logRecord) && bufMsg.compare(logRecord.msg) == 0) {
    printf("Message in ktest_write_train matches log \n");
  } else {
    //This is a hack to make sure the log and verifier produced roughly the same type of message.
    //Unfortunately the message string is produced by vsnprintf, and we can't fully generate the
    //strings accurately without var args modeling.
    if ((bufMsg.find("startgame") != std::string::npos && logRecord.msg.find("startgame") != std::string::npos) ||
	(bufMsg.find("lvl") != std::string::npos && logRecord.msg.find("lvl") != std::string::npos)||
	(bufMsg.find("team") != std::string::npos && logRecord.msg.find("team") != std::string::npos) ||
	(bufMsg.find("sb ") != std::string::npos && logRecord.msg.find("sb ") != std::string::npos)
	) {
      printf("Msg type matches: need to implement vsnprintf to fully verify numbers in string\n");fflush(stdout);
    } else {
      
      printf("ERROR: message in buf:%s| doesn't match message in log:%s|\n", bufMsg.c_str(), logRecord.msg.c_str());
      fflush(stdout);
      std::exit(EXIT_FAILURE);
    }
  }

  if (trainType == TASETrainType::ML) {

  }

  
  if (trainType == TASETrainType::CLUSTER ) {
    //We've just reached the end of a verification fragment.  Record
    //the message and constraints, and print everything to a log.

    //We're just writing the cluster when we get to a send since the sb and lvl messages are send with
    //the partial updates.
    if (logRecord.type != sbC2S && logRecord.type != lvlC2S ) {
      clusterEndType = "SEND";
      //Don't make a record unless there's actually a a fragment.
      if (execution_fragment.size() > 0) {
	std::string clusterLogName = "cluster_log_seed_" + std::to_string(random_seed_init);
	resetAndWriteCluster((void *) bufMsg.c_str(), bufMsg.length(),clusterLogName );
      }
    }
  }

  //There's no logic for the ML trainType in here because we produce those record in trainingFork();
  
}

//extern void worker_success1 (WorkerGroup * Stopped, WorkerGroup * Running);
void model_tetri_ktest_write_singleMsgVerification(std::string bufMsg) {
  LOG_TASE("Entering model_tetri_ktest_write_SingleMsgVerififcation \n");
  LOG_TASE("partialUpdateMsgCtr is %d \n", partialUpdateMsgCtr);LOG_FLUSH();
  if (!inPriorityTest) {
    //If msg is a partial update, update the ctr for the singleMsgVerification test
    //if (bufMsg.find("p 1") != std::string::npos) {
    //  partialUpdateMsgCtr++;
    //}

    if (bufMsg.find("p 1") != std::string::npos) {
      LOG_TASE("Condition 1 is true \n");LOG_FLUSH();
      msgCtr++;
      LOG_TASE("msgCtr is %d \n", msgCtr);LOG_FLUSH();
    } else {
      LOG_TASE("Condition 1 is false \n");LOG_FLUSH();
    }

    LOG_TASE("singleMsgVerificationIdx is %d \n", singleMsgVerificationIdx);LOG_FLUSH();

    if (bufMsg.find("p 1") != std::string::npos && partialUpdateMsgCtr == singleMsgVerificationIdx -1 ) {
    //if (bufMsg.find("p 1") != std::string::npos && partialUpdateMsgCtr == singleMsgVerificationIdx -1) {
      /*
      struct TetriNETLogRecord r = getNextTetriLogEntry();
      if (r.type != puC2S) {
	LOG_TASE("Wrong tetrinet log record type in ktest_write_singlemsgver\n");LOG_FLUSH();
	exit(0);
      }
      */
      //Start the single msg verification test here:
      LOG_TASE("Attempting to start test ...\n"); fflush(stdout);
      model_tetri_ktest_write_replay(bufMsg); //Updates log to check current bufmsg against log
      next_msg_to_verify = peekNextC2SPartialUpdate().msg;
      LOG_TASE("STARTING SINGLE MESSAGE PRIORITY TEST \n");
      single_msg_test_start_time = util::getWallTime();
      LOG_TASE("Msg to verify is %s \n", next_msg_to_verify.c_str());fflush(stdout);
      //int pidRet = singleMessagePriorityTestTetrinet();
      inPriorityTest = true;
      /* if (pidRet != 0) {
	printf("Exiting after single message priority test \n");fflush(stdout);
	//worker_exit();
	//tase_exit();
	std::exit(EXIT_FAILURE);
      } else {
	printf("First child advancing with pid %d \n", getpid()); fflush(stdout);
      }
      */
    } else {
      //If we haven't reached the message we're testing, just keep replaying.
      model_tetri_ktest_write_replay(bufMsg);
    }
    

  } else { //We're already in the priority test:

    //We only care about reaching the next partial update message, so just continue if
    //this call is producing some other sort of msg (e.g., sb or lvl)
    if (bufMsg.find("p 1") == std::string::npos) {
      //Nothing to do
    } else {
      if (next_msg_to_verify.compare(bufMsg) == 0) {
	LOG_TASE("Worker %d verified msg \n", getpid());fflush(stdout);
	LOG_TASE("SINGLE MSG TEST: Verified msg %d in %lf seconds \n", (int) singleMsgVerificationIdx, util::getWallTime() - single_msg_test_start_time); fflush(stdout);

	//If we're doing synthetic path training, we need to see if the current verification was better than
	//the best we've found so far.
	
	if (updateSyntheticPaths) {
	  GlobalExecutorPtr->processSyntheticPath((int) singleMsgVerificationIdx);
	}
	
	worker_success(Stopped, Running);
	msgCtr++;
	exit(0);

      } else {
	LOG_TASE("Worker found incorrect message %s \n", bufMsg.c_str());
	//deathsig();
	exit(0);
      }
    }
  }
}

void model_tetri_ktest_write_verification(std::string bufMsg) {
  //We need a path oracle that can verify all msgs to implement this.
  //Coming soon.
  //We only care about reaching the next partial update message, so just continue if
  //this call is producing some other sort of msg (e.g., sb or lvl)
  struct TetriNETLogRecord r = getNextTetriLogNetworkMsg();
  if (r.type != puC2S && r.type != sbC2S && r.type != lvlC2S && r.type != otherC2S) {
    LOG_TASE("Wrong tetrinet log record type in ktest_write_ver\n");LOG_FLUSH();
    exit(0);
  }

  
  if (bufMsg.find("p 1") == std::string::npos) {
    //Nothing to do
  } else {

    std::string nextVerMsg = r.msg;
    LOG_TASE("nextVerMsg is %s \n", nextVerMsg.c_str());LOG_FLUSH();
    if (nextVerMsg.compare(bufMsg) == 0) {
      LOG_TASE("Worker %d verified msg %d \n", getpid(), msgCtr);fflush(stdout);

      if (TASEKillConsAfterVer) {
	GlobalExecutionStatePtr->constraints.clear();
      }
      LOG_TASE("Calling worker reset feats \n");LOG_FLUSH();
      workerResetFeats();
      worker_success(Stopped, Running);
      //resetBranches();
      //clearExecutionFragment();
      
      msgCtr++;
      //next_msg_to_verify = peekNextC2SPartialUpdate().msg;
    } else {
      LOG_TASE("Worker found incorrect message %s \n", bufMsg.c_str());
      //deathsig();
      exit(0);
    }
  }
  
}


// //Todo - carefully check branchesSinceLastMsg and executionFragment logic
// void populate_tetrinet_worker_feats(struct TetriNETWorkerFeats * feats, pid_t pid, std::vector<uint64_t> frags){
//   feats->pid = (uint64_t) pid;
//   float xVal = 0;
//   float yVal = 0;
//   float rotVal =0;
//   #ifdef TASE_TETRINET
//   //readTetrinetBaseFeats(&xVal, &yVal, &rotVal, next_msg_to_verify); fixme for lstm
//   feats->currPiece = (uint64_t) current_piece; //This is sometimes out of sync with the current msg
//   #endif
//   feats->x = (uint64_t) xVal;
//   feats->y = (uint64_t) yVal;
//   feats->rotation = (uint64_t) rotVal;
//   feats->BBRIP =  target_ctx_gregs[GREG_RIP].u64; //Needs to be updated if we branch in interp fn.
//   feats->branchesSinceLastMsg = branchesSinceLastMsg; //Todo -Make sure this is updated
//   feats->executionFragmentSize = frags.size();
//   for (int i = 0; i < frags.size(); i++) {
//     feats->executionFragment[i] = frags[i];
//     if (taseDebug) 
//       printf("Writing fragment to shared buf with ID 0x%lx, as base 10 %lu \n", frags[i], frags[i] );fflush(stdout);
//   }
//   if (taseDebug)
//     printf("Leaving populate_tetrinet_worker_feats \n");fflush(stdout);
// }

//char *sgets(char *buf, int len, int s)
void Executor::model_tetri_sgets() {

  MOD_TASE("Entering model_tetri_sgets \n");

  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);

  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) &&
       (isa<ConstantExpr>(arg3Expr))
       ){

    char * in_buf = (char *) target_ctx_gregs[GREG_RDI].u64;
    int len = (int) target_ctx_gregs[GREG_RSI].i32;
    
    if ( verTestType == VerTestType::REPLAY ) {
      struct TetriNETLogRecord r = getNextTetriLogEntry();
      if (r.type == S2C) {
	strcpy(in_buf, r.msg.c_str() );
      } else {
	LOG_TASE("ERROR: Found msg %s in log for sgets during replay \n", r.msg.c_str());
	std::exit(EXIT_FAILURE);
      }
    } else if ( verTestType == VerTestType::TRAIN ) { 
      struct TetriNETLogRecord r = getNextTetriLogEntry();
      if (r.type == S2C) {
	strcpy(in_buf, r.msg.c_str() );
      } else {
	LOG_TASE("ERROR: Found msg %s in log for sgets during train \n", r.msg.c_str());
	std::exit(EXIT_FAILURE);
      }
    } else if ( verTestType == VerTestType::SINGLEMSGVER ) {
      if (inPriorityTest) {
      //if (inSingleMsgVerificationTest) {
	//If we're in a singleMsgVerification test, assume we're trying to reach a C2S with no
	//preceeding S2C messages.  That implies this is a dead end.
	//deathsig();
	LOG_TASE("Exiting singleMsgVerificationTest due to hitting a S2C message \n");
	exit(0);
	
      } else {
	struct TetriNETLogRecord r = getNextTetriLogEntry();
	if (r.type == S2C) {
	  strcpy(in_buf, r.msg.c_str() );
	} else {
	  LOG_TASE("ERROR: Found msg %s in log for sgets during replay \n", r.msg.c_str());
	  std::exit(EXIT_FAILURE);
	}
      }
    } else if ( verTestType == VerTestType::VERIFY ) {
      struct TetriNETLogRecord r = getNextTetriLogNetworkMsg(); //FULL VERIFICATION
      if (r.type != S2C) {
	LOG_TASE("Error: found wrong type of network msg:%s in sgets \n",r.msg.c_str()); 
	//deathsig();
	std::exit(EXIT_FAILURE);
      } else {
	strcpy(in_buf, r.msg.c_str());
      }
    } else {
      LOG_TASE("ERROR: verTestType unspecified \n");
      std::exit(EXIT_FAILURE);
    }

    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) in_buf, Expr::Int64);
    tase_helper_write( (uint64_t) &target_ctx_gregs[GREG_RAX].u64, resExpr);
    do_ret();
    
  } else {
    LOG_TASE("ERROR in model_tetri_sgets - symbolic arg \n");
    std::cout.flush();
    std::exit(EXIT_FAILURE);
  }
}

#define TETRI_SOCK_FD 3
//Should be good to set random_seed and random_seed_init here
//Also round length
extern int max_round;
extern int random_seed;
extern int random_seed_init;
extern "C" void tetrinet_save_random_seed_initial_val();
void Executor::model_tetri_conn() {
  //random_seed = tetrinetRandomSeed;
  //random_seed_init = tetrinetRandomSeed;
  tetrinet_save_random_seed_initial_val(); //Save the initial seed value as a feat for ML.  It gets modified later
  //max_round = tetrinetMaxRound;
  
  MOD_TASE("Entering model_tetri_conn \n");

  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);

  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) &&
       (isa<ConstantExpr>(arg3Expr))
       ){

    uint64_t res = (uint64_t) TETRI_SOCK_FD;
    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    tase_helper_write( (uint64_t) &target_ctx_gregs[GREG_RAX].u64, resExpr);
    do_ret();
  }  else {
    LOG_TASE("ERROR in model_tetri_conn - symbolic arg \n");
    std::cout.flush();
    std::exit(EXIT_FAILURE);
  }
}

bool emitMessageBranchMapInTraining = true;
void printMessageBranchMap(std::map<int,int> mapping, FILE * output);
void Executor::model_tetri_shutdown() {
  LOG_TASE("Entering model_tetri_shutdown \n"); fflush(stdout);
  //Are there any more C2S messages we missed?
  //printf("PID %d Doing something with keyLog \n", getpid());fflush(stdout);
  //printf(" PID %d sees loc as %d \n", getpid(), keyLog.tellg());fflush(stdout);
  //printf("Doing something with keyLog \n");fflush(stdout);
  std::string line;

  //Fix/merge in later. -ABH 01/29/2024
  //This should really be a different flag, like "makeMessageBranchInitFile

  if (verTestType == VerTestType::TRAIN && makeInitialBranchMap) {
    //Dump our best (i.e, shortest) branch info so far.
    std::string mapFileName = "MESSAGE_BRANCH_SEED_" + std::to_string(random_seed_init) + "_INIT";
    FILE * mapFile = fopen(mapFileName.c_str() ,"w+");
    printMessageBranchMap( initialMessageBranchMap, mapFile );
  }
  /*
  if (verTestType.compare("train") == 0 && syntheticPathTraining) {
    //Dump our best (i.e, shortest) branch info so far.
    std::string mapFileName = "MESSAGE_BRANCH_SEED_" + std::to_string(random_seed_init) + "_INIT";
    FILE * mapFile = fopen(mapFileName.c_str() ,"w+");
    if (emitMessageBranchMapInTraining && syntheticPathTraining) {
      printMessageBranchMap( initialMessageBranchMap, mapFile );
    }
  }


  if (priorityLSTMTest && inPriorityTest ) {
    //exit I guess?
    printf("PID %d hit shutdown \n", getpid());fflush(stdout);
    deathsig();
    exit(0);
  }


  while (std::getline(keyLog, line)) {
    if (line.find("C2S") != std::string::npos) {
      if (priorityLSTMTest && inPriorityTest ) {
	//exit I guess?
	printf("PID %d hit shutdown \n", getpid());fflush(stdout);
	deathsig();
	exit(0);
      }  else {
	printf("VERIFICATION ENDED: Failed to verify msg %s \n", line.c_str());
	fflush(stdout);
	tase_exit();
      }
    }
  }
  */
  if ( verTestType == VerTestType::SINGLEMSGVER ) {
    printf("model_shutdown encountered during single msg verification test. Shutting down. \n"); fflush(stdout);
    exit(0);
  }

  if (partialUpdateMsgCtr == msgsToVerify) {
    
    LOG_TASE("VERIFICATION ENDED: SUCCESS \n");
    //printf("%lu basic blocks were concrete out of %lu basic blocks total \n", concInterpCtr, interpCtr);
    fflush(stdout);
 
    worker_success(Stopped, Running);
  } else {
    LOG_TASE("Worker %d failed: Entered shutdown after verifying only %d pieces \n", getpid(), partialUpdateMsgCtr);
    LOG_FLUSH();
    exit(0);
  }
  
  //if (priorityLSTMTest) {
  LOG_TASE("EVAL: ctr %d: Ran through as replay \n", singleMsgVerificationIdx);fflush(stdout);
  std::exit(EXIT_FAILURE);
  //worker_exit();
    //} else {
    //tase_exit();
    //}
}

//Skip srand since the seed is explicitly provided by the client
void Executor::model_srand() {
  MOD_TASE("Skipping s_rand call \n");
  do_ret();
}

   
//We should fix this.  We need to figure out how to model var args or
//find another workeraround.
void Executor::model_tetri_vsnprintf() {
  static int ctr = 0;
  MOD_TASE("Entering model_tetri_vsnprintf \n");

  if ( ( priorityLSTMTest && inPriorityTest ) || verTestType == VerTestType::VERIFY  ) {
    MOD_TASE("PID %d hit vsnprintf \n", getpid());
    //MOD_TASE("Current x/y/rot: %d, %d, %d \n", current_x, current_y, current_rotation);
    char * firstPart = (char *) malloc(12);
    strncpy(firstPart, (char *) target_ctx_gregs[GREG_RDX].u64, 10);
    if (strcmp(firstPart, "playerlost") == 0) {
      LOG_TASE("Worker found playerlost message. Exiting \n");
      //deathsig();
      exit(0);
    }

  }
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);
  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) &&
       (isa<ConstantExpr>(arg3Expr))
       ){
    printf("format is %s\n", (char *) target_ctx_gregs[GREG_RDX].u64);
    char * firstChars = (char *) malloc (10);
    strncpy(firstChars, (char *) target_ctx_gregs[GREG_RDX].u64, 4);
    printf("First chars: %s\n", firstChars);
    fflush(stdout);
    if (strcmp(firstChars, "team") == 0) {
      int arg4 = (int) target_ctx_gregs[GREG_RCX].i32;
      printf("arg4 appears to be %d \n", arg4);
      uint64_t res = sprintf((char *)  target_ctx_gregs[GREG_RDI].u64, "team %d ", 1);
      target_ctx_gregs[GREG_RAX].u64 = res;
    } else if (strcmp(firstChars, "star") == 0) {
      int arg4 = (int) target_ctx_gregs[GREG_RCX].i32;
      int arg5 = (int) target_ctx_gregs[GREG_R8].i32;

      //uint64_t res = sprintf((char *)  target_ctx_gregs[GREG_RDI].u64, "startgame %d %d", arg4, arg5);
      uint64_t res = sprintf((char *)  target_ctx_gregs[GREG_RDI].u64, "startgame 1 %d", arg4);
      target_ctx_gregs[GREG_RAX].u64 = res;
    } else if ( strcmp(firstChars, "lvl ") == 0) {

      int arg4 = (int) target_ctx_gregs[GREG_RCX].i32;
      int arg5 = (int) target_ctx_gregs[GREG_R8].i32;
      uint64_t res = sprintf((char *)  target_ctx_gregs[GREG_RDI].u64, "lvl %d %d", arg4, arg5);
      target_ctx_gregs[GREG_RAX].u64 = res;
    } else if ( strcmp(firstChars, "sb 0") == 0) {
      //Don't even try...
      uint64_t res = sprintf((char *)  target_ctx_gregs[GREG_RDI].u64, "sb 0 cs%d %d", 1, 1);
      target_ctx_gregs[GREG_RAX].u64 = res;
    }
    else {
      printf("ERROR: Need to implement vsnprintf \n");
      std::exit(EXIT_FAILURE);
    }
    do_ret();
    ctr++;
  } else {
    printf("Error: symbolic args passed into vsnprintf \n");
    fflush(stdout);
    //worker_exit();
    std::exit(EXIT_FAILURE);
  }
}

uint64_t tetrinetX;
uint64_t tetrinetY;
uint64_t tetrinetRot;

void getTetrinetBaseFeats(uint64_t * xVal, uint64_t * yVal, uint64_t * rotVal, uint64_t * branchesVal, uint64_t * currPieceVal){
  printf("Entering getTetrinetBaseFeats\n");fflush(stdout);
  *xVal = tetrinetX;
  *yVal = tetrinetY;
  *rotVal = tetrinetRot;
  *branchesVal = branchesSinceLastMsg;
  *currPieceVal = (uint64_t) current_piece;
}

void readTetrinetBaseFeats(float * xVal , float * yVal, float * rotVal, std::string nextMsg) {
  //LOG_TASE("DBG Entering readTetrinetBaseFeats on msg %s \n", nextMsg.c_str());LOG_FLUSH();
  int x;
  int y;
  int rot;
  
  if (nextMsg.find("p 1") == std::string::npos) {
    LOG_TASE("ERROR: Record %s isn't C2S in readTetrinetBaseFeats: \n", nextMsg.c_str());
    LOG_FLUSH();
    std::exit(EXIT_FAILURE);
  }

  const char * constMsgCStr = nextMsg.c_str();
  char * msgCStr = (char *) malloc(strlen(constMsgCStr) +1);
  strcpy (msgCStr, constMsgCStr);
  //printf("Raw msg %d appears to be %s \n",msgCtr ,msgCStr);
  //fflush(stdout);
  //LOG_TASE("DBG 2 \n");LOG_FLUSH();
  //char * base = strtok(msgCStr, " "); //C2S
  //char * trash = strtok(NULL, " "); //MSG:
  //char * trash = strtok(NULL, " "); //p
  char * trash = strtok(msgCStr, " "); //p
  //LOG_TASE("DBG 3 \n");LOG_FLUSH();
  trash = strtok(NULL, " "); //1
  //LOG_TASE("DBG 3 \n");LOG_FLUSH();
  char * xStr = strtok(NULL, " ");//x
  char * yStr = strtok(NULL, " ");//y
  char * rotStr = strtok(NULL, " ");//rot

  x = atoi(xStr);
  y = atoi(yStr);
  rot = atoi(rotStr);

  *xVal = (float) x;
  *yVal = (float) y;
  *rotVal = (float) rot;
  
}

//Possibly reset branchesSinceLastMsg here to make it cleaner
void setTetrinetBaseFeats() {
  std::string nextMsg =  peekNextC2SPartialUpdate().msg;
  int x;
  int y;
  int rot;

  if (nextMsg.find("C2S MSG: p ") == std::string::npos  && nextMsg.find("C2S MSG: lvl") == std::string::npos) {
    printf("ERROR: Next msg isn't C2S.  Something went wrong on test branch with message %s \n", nextMsg.c_str());
    fflush(stdout);
    std::exit(EXIT_FAILURE);
  }

  const char * constMsgCStr = nextMsg.c_str();
  char * msgCStr = (char *) malloc(strlen(constMsgCStr) +1);
  strcpy (msgCStr, constMsgCStr);
  //printf("Raw msg appears to be %s \n", msgCStr);
  //fflush(stdout);

  char * base = strtok(msgCStr, " "); //C2S
  char * trash = strtok(NULL, " "); //MSG:
  trash = strtok(NULL, " "); //p
  trash = strtok(NULL, " "); //1

  char * xStr = strtok(NULL, " ");//x
  char * yStr = strtok(NULL, " ");//y
  char * rotStr = strtok(NULL, " ");//rot

  x = atoi(xStr);
  //x = x-6; //Center the features around the starting x coordinate, 6
  y = atoi(yStr);
  rot = atoi(rotStr);

  tetrinetX = (uint64_t) x;
  tetrinetY = (uint64_t) y;
  tetrinetRot = (uint64_t) rot;

}



//These drawing methods are pretty much ripped from tetrinet.  They're here to help us visualize
//whether or not path selection is working by providing snapshots of what the screen looks like.
//-ABH

#ifdef TASE_TETRINET


extern "C" void  klee_stub_draw_own_field();

#define FIELD_WIDTH     12
#define FIELD_HEIGHT    22
typedef char Field[FIELD_HEIGHT][FIELD_WIDTH];
extern Field fields[6];        /* Current field states */
extern int my_playernum;
extern int playing_game;
extern int cast_shadow;
extern int current_x;
extern int current_y;


typedef struct {
  int hot_x, hot_y;   /* Hotspot coordinates */
  int top, left;      /* Top-left coordinates relative to hotspot */
  int bottom, right;  /* Bottom-right coordinates relative to hotspot */
  char shape[4][4];   /* Shape data for the piece */
} PieceData;

extern PieceData piecedata[7][4];

static const int own_coord[2] = {1,0};

extern int current_piece, current_rotation;
/* Information for drawing blocks.  Color attributes are added to blocks in
 * the setup_fields() routine. */
static int tile_chars[15] =
  { ' ','#','#','#','#','#','a','c','n','r','s','b','g','q','o' };


#define MAXCOLORS       256

static int colors[MAXCOLORS][2] = { {-1,-1} };

/* Return a color attribute value. */

static long getcolor(int fg, int bg)
{
  int i;

  if (colors[0][0] < 0) {
    start_color();
    memset(colors, -1, sizeof(colors));
    colors[0][0] = COLOR_WHITE;
    colors[0][1] = COLOR_BLACK;
  }
  if (fg == COLOR_WHITE && bg == COLOR_BLACK)
    return COLOR_PAIR(0);
  for (i = 1; i < MAXCOLORS; i++) {
    if (colors[i][0] == fg && colors[i][1] == bg)
      return COLOR_PAIR(i);
  }
  for (i = 1; i < MAXCOLORS; i++) {
    if (colors[i][0] < 0) {
      if (init_pair(i, fg, bg) == ERR)
	continue;
      colors[i][0] = fg;
      colors[i][1] = bg;
      return COLOR_PAIR(i);
    }
  }
  return -1;
}


/* Redraw everything on the screen. */
FILE * screenLog;
static void screen_refresh(void)
{
  /*
  if (gmsg_inputwin)
    touchline(stdscr, gmsg_inputpos, gmsg_inputheight);
  if (plinebuf.win)
    touchline(stdscr, plinebuf.y, plinebuf.height);
  if (gmsgbuf.win)
    touchline(stdscr, gmsgbuf.y, gmsgbuf.height);
  if (attdefbuf.win)
    touchline(stdscr, attdefbuf.y, attdefbuf.height);
  */
  putwin(stdscr, screenLog);
  wnoutrefresh(stdscr);
  doupdate();
}


static void draw_own_field(FILE * log)
{
  int x, y, x0, y0;
  Field *f = &fields[my_playernum-1];
  int shadow[4] = { -1, -1, -1, -1 };

  //if (dispmode != MODE_FIELDS)
  //return;

  /* XXX: Code duplication with tetris.c:draw_piece(). --pasky */
  if (playing_game && cast_shadow) {
    int y = current_y - piecedata[current_piece][current_rotation].hot_y;
    char *shape = (char *) piecedata[current_piece][current_rotation].shape;
    int i, j;

    for (j = 0; j < 4; j++) {
      if (y+j < 0) {
	shape += 4;
	continue;
      }
      for (i = 0; i < 4; i++) {
	if (*shape++)
	  shadow[i] = y + j;
      }
    }
  }

  x0 = own_coord[0]+1;
  y0 = own_coord[1];
  fprintf(log,"next\n");
  for (int i = 0; i < 10; i++) {
    fprintf(log,"\n");
  }
  fprintf(log,"--------------\n");
  for (y = 0; y < 22; y++) {
    fprintf(log,"|");
    for (x = 0; x < 12; x++) {
      int c = tile_chars[(int) (*f)[y][x]];

      if (playing_game && cast_shadow) {
	PieceData *piece = &piecedata[current_piece][current_rotation];
	int piece_x = current_x - piece->hot_x;

	if (x >= piece_x && x <= piece_x + 3
	    && shadow[(x - piece_x)] >= 0
	    && shadow[(x - piece_x)] < y
	    && ((c & 0x7f) == ' ')) {
	  c = (c & (~0x7f)) | '.'
	    | getcolor(COLOR_BLACK, COLOR_BLACK) | A_BOLD;
	}
      }

      mvaddch(y0+y*2, x0+x*2, c);
      addch(c);
      mvaddch(y0+y*2+1, x0+x*2, c);
      addch(c);
      fprintf(log,"%c", c); //ABH
    }
    fprintf(log,"|");
    fprintf(log,"\n"); //ABH
  } //1
  fprintf(log,"\n");//ABH
  fprintf(log,"--------------\n");
  fprintf(log,"\n");//ABH

  fprintf(log,"end\n");
  for (int i = 0; i < 10; i++) {
    fprintf(log,"\n");
  }

  /*
  if (gmsg_inputwin) {
    delwin(gmsg_inputwin);
    gmsg_inputwin = NULL;
    draw_gmsg_input(NULL, -1);
  }
  */
  //if (!field_redraw) {
  (void)curs_set(0);
  screen_refresh();
  //}
  fflush(log);
}

#endif
  
//This messageBranch map logic is used to help us iteratively train with the LSTM.
//The idea is that we train the LSTM, evaluate it on a dataset, and then retrain
//using the new paths produced by the LSTM inserted back into the
//original data set in place of the old paths when the LSTM's new path is shorter.

void updateMessageBranchMap(std::map<int,int> * theMap, int msg, int branches) {
  std::map<int,int>::iterator it =  theMap->find(msg);
  if (it != theMap->end()) {
    LOG_TASE("Found old mapping \n");LOG_FLUSH();
    it->second = branches;
  } else {
    LOG_TASE("Making new mapping for %d %d \n", msg, branches);LOG_FLUSH();
    theMap->insert(std::make_pair(msg, branches));
  }
}

//Load pairs of ints, assuming the first int on each line is message ctr and second is branch depth


void loadBestMessageBranchMap( const char * logName) {
  std::ifstream mapLog = std::ifstream(logName);
  std::string line;

  while(std::getline(mapLog, line)) {
    char * cline = new char[strlen(line.c_str()) +1 ]; //shoot me
    strcpy (cline, line.c_str());
    char * tok1 = strtok(cline, " ");
    int i1 = atoi(tok1);
    char * tok2 = strtok(0, " ");
    int i2 = atoi(tok2);
    printf("%s %s \n", tok1, tok2);fflush(stdout);
    printf("%d %d \n", i1, i2);fflush(stdout);
    bestMessageBranchMap.insert(std::make_pair(i1,i2));
    free(cline);

  }
  printf("Loaded message branch map with %ld entries \n", bestMessageBranchMap.size());
}


void printMessageBranchMap(std::map<int,int> mapping, FILE * output) {
  std::map<int,int>::iterator it;
  LOG_TASE("Entering printMessageBranchMap with size %ld \n", mapping.size());LOG_FLUSH();

  for (it = mapping.begin(); it != mapping.end();it++) {
    LOG_TASE("Looping \n");LOG_FLUSH();
    int msgCtr = it->first;
    int branches = it->second;
    LOG_TASE("msgCtr and branches are %d and %d\n", msgCtr, branches);LOG_FLUSH();
    fprintf(output,"%d %d\n", msgCtr, branches);
    fflush(output);
  }
  fflush(stdout);
  LOG_TASE("Exiting printMessageBranchMap \n");LOG_FLUSH();
}

int MLParentID = 0;


// void Executor::dumpFeatures(bool isValidState,  int ID) {
//   printf("Double check dumpFeatures after refactor! \n");fflush(stdout);
//   std::exit(EXIT_FAILURE);
  
//   printf("Writing features with isValidState %d \n", (int) isValidState);
//   fflush(stdout);
//   std::string logName;

//   logName = "FeatureLog.txt";

//   if (featLog == NULL) {
//     featLog = fopen(logName.c_str(), "a+");
//   }

//   if (int(isValidState) == 1 && makeInitialBranchMap) {
//     printf("Updating message branch map with %d %d \n", msgCtr, mlInfo.branchesSinceLastMsg);fflush(stdout);
//     updateMessageBranchMap(&initialMessageBranchMap,msgCtr, mlInfo.branchesSinceLastMsg);
//   }

//   fprintf(featLog, "%d,", int(isValidState));
//   fprintf(featLog, "%d,", ID);
//   fprintf(featLog, "%d,", MLParentID);
// #ifdef TASE_TETRINET
//   fprintf(featLog, "%d,", random_seed_init);
// #endif
//   fprintf(featLog, "%d,", msgCtr);
//   fprintf(featLog, "%d,", getMLBBID(pre_interp_RIP));
//   fprintf(featLog, "%d,", getMLBBID(target_ctx_gregs[GREG_RIP].u64));
//   printf("Mapping RIP 0x%lx to MLBBID %ld \n", target_ctx_gregs[GREG_RIP].u64, getMLBBID(target_ctx_gregs[GREG_RIP].u64)); fflush(stdout);
//   fprintf(featLog, "%d,", branchDepth);
//   fprintf(featLog, "%d,", mlInfo.branchesSinceLastMsg);
//   fprintf(featLog, "%d,", branchType);
//   fprintf(featLog, "%d,", last_IR_branch_type);
//   int isTerminalBranch = 0;
//   if (badBranchDepth == maxBadBranchDepth) {
//     isTerminalBranch =1;
//   }
//   fprintf(featLog, "%d,", isTerminalBranch);
//   std::string nextMsg = getNextMsgString();
//   fprintf(featLog, "%s,", nextMsg.c_str());

// #ifdef TASE_TETRINET
//   //Break up partial updates into fields
//   std::string partialUpdateChars ("C2S MSG: p 1 ");
//   if (nextMsg.find(partialUpdateChars) != std::string::npos) {
//     //Sample msg: "C2S MSG: p 1 2 21 0"

//     std::vector<std::string> toks;
//     std::stringstream strm (nextMsg);
//     std::string currStr;

//     while (getline(strm, currStr, ' ')) {
//       toks.push_back(currStr);
//     }

//     if (toks.size() != 7) {
//       printf("Unexpected number %d of tokens in C2S partial update msg: %s", toks.size(), nextMsg.c_str());
//       fflush(stdout);
//       //worker_exit();
//       //tase_exit();
//       std::exit(EXIT_FAILURE);
//     }

//     fprintf(featLog, "%s,", toks[4].c_str());
//     fprintf(featLog, "%s,", toks[5].c_str());
//     fprintf(featLog, "%s,", toks[6].c_str());
//     fprintf(featLog, "%d,", current_piece);

//   } else {
//     fprintf(featLog, "-1,-1,-1,-1,");
//   }
// #endif

//   if (useConstraintBOW) {
//     for (int i =0; i < constraint_features.size(); i++) {
//       fprintf(featLog, "%lf,", constraint_features[i]);
//     }
//     for (int i =0; i < recent_constraint_features.size(); i++) {
//       fprintf(featLog, "%lf,", recent_constraint_features[i]);
//     }
//   }

//   if (useBBBOW) {
//     for (int i = 0; i < BBBowVec.size(); i++) {
//       fprintf(featLog, "%d,", BBBowVec[i]);
//     }
//   }
  
//   fprintf(featLog, "\n");
//   fflush(featLog);
//   MLParentID = ID;
//   printf("Returning from dumpFeatures \n");
//   fflush(stdout);
// }
FILE * messageBranchMapFile;
void Executor::dumpFeaturesTetriNET(bool isValidState,  int ID, uint64_t MLBBID) {
  LOG_TASE("Writing features with isValidState %d \n", (int) isValidState);
  LOG_FLUSH();
  std::string logName;

  logName = "FeatureLog.txt";

  if (featLog == NULL) {
    featLog = fopen(logName.c_str(), "a+");
  }

  if (int(isValidState) == 1 && makeInitialBranchMap) {
    LOG_TASE("Updating message branch map with %d %d \n", partialUpdateMsgCtr, branchesSinceLastMsg);fflush(stdout);
    updateMessageBranchMap(&initialMessageBranchMap,partialUpdateMsgCtr, branchesSinceLastMsg);
    //Dump our best (i.e, shortest) branch info so far.
    std::string mapFileName = "MESSAGE_BRANCH_SEED_" + std::to_string(random_seed_init) + "_INIT";
    if (messageBranchMapFile == NULL) {
      
      messageBranchMapFile = fopen(mapFileName.c_str() ,"w+");
    }
    printMessageBranchMap( initialMessageBranchMap, messageBranchMapFile );
  }

  fprintf(featLog, "%d,", int(isValidState));  //0
  fprintf(featLog, "%d,", ID);  //1
  fprintf(featLog, "%d,", MLParentID); //2
  fprintf(featLog, "%d,", random_seed_init);//3
  fprintf(featLog, "%d,", partialUpdateMsgCtr);//4
  //fprintf(featLog, "%ld,", getMLBBID(pre_interp_RIP)); //Removed since we never use it anywhere
  fprintf(featLog, "%ld,", 0);//5
  fprintf(featLog, "%ld,", MLBBID);//6
  fprintf(featLog, "%d,", branchDepth);//7
  fprintf(featLog, "%d,", branchesSinceLastMsg);//8
  fprintf(featLog, "%d,", branchType);//9
  fprintf(featLog, "%d,", last_IR_branch_type);//10
  int isTerminalBranch = 0;
  if (badBranchDepth == maxBadBranchDepth) {
    isTerminalBranch =1;
  }
  fprintf(featLog, "%d,", isTerminalBranch); //11
  //std::string nextMsg = getNextMsgString();
  //fprintf(featLog, "%s,", nextMsg.c_str());
  std::string nextMsg = peekNextC2SPartialUpdate().msg;
  fprintf(featLog, "%s,", nextMsg.c_str());//12

  std::string partialUpdateChars ("p 1 ");
  if (nextMsg.find(partialUpdateChars) != std::string::npos) {
    float x,y,rot;

    readTetrinetBaseFeats(&x,&y,&rot, nextMsg);
    LOG_TASE("Returned from readTetrinetBaseFeats"); LOG_FLUSH();
    fprintf(featLog, "%d,", (int) x);//13
    fprintf(featLog, "%d,", (int) y);//14
    fprintf(featLog, "%d,", (int) rot);//15
    //fprintf(featLog, "%d,", current_piece);//16 //Piece doesn't always
    //update prior to initial branching when entering new round so pull
    //the value from our computed list
    fprintf(featLog, "%d,", (int) getNthTetrinetMessagePieceID (partialUpdateMsgCtr)); //16
  } else {
    fprintf(featLog, "-1,-1,-1,-1,"); //13-16
  }


  if (useConstraintBOW) {
    for (int i =0; i < constraint_features.size(); i++) {
      fprintf(featLog, "%lf,", constraint_features[i]); //17-48
    }
    for (int i =0; i < round_constraint_features.size(); i++) {
      fprintf(featLog, "%lf,", round_constraint_features[i]); //49-80
    }
  }

  if (useBBBOW) {
    for (int i = 0; i < BBBowVec.size(); i++) {
      fprintf(featLog, "%d,", BBBowVec[i]); //Depends on size of BBBows
    }
  }

  fprintf(featLog, "\n");
  fflush(featLog);
  MLParentID = ID;
  LOG_TASE("Returning from dumpFeatures \n");LOG_FLUSH();
  
}

int Executor::getCurrentBranchDest(bool isTrueBranch) {
  KInstruction * ki = GlobalExecutionStatePtr->prevPC;
  BranchInst *bi = cast<BranchInst> (ki->inst);
  BasicBlock * dst;
  if (isTrueBranch) {
    dst = bi->getSuccessor(0);
  } else {
    dst = bi->getSuccessor(1);
  }
  KFunction * interpFn = GlobalExecutionStatePtr->stack.back().kf;
  unsigned idx = interpFn->basicBlockEntry[dst];
  return idx;
}

//Check: do we return 0 or PID if the condition is TRUE?  Same question for FALSE. Does it even matter?
extern uint64_t pre_interp_RIP;
int Executor::forkOnPossibleIRBranchesTetriNET( ref<Expr> condition, std::vector<std::vector<float>> IR_Constraint_BOWs) {
  branchType = 1;
  DBG_TASE("Entering forkOnPossibleIRBranches \n");
  LOG_TASE("Entering forkOnPossibleIRBranchesTetriNET \n");LOG_FLUSH();
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
  DBG_TASE("%lf seconds elapsed in toUniquePreCalc without cheat \n", util::getWallTime() -uniqueTime);
  LOG_TASE("DBG 22 \n");LOG_FLUSH();
  if (isa<ConstantExpr> (condition)) {
    //We shouldn't ever reach this line of code because of the solver call in Executor::fork
    LOG_TASE("Sanity check failed in forkOnPossibleIRBranches \n"); LOG_FLUSH();
    std::exit(EXIT_FAILURE);
    return 0; 
  }
  LOG_TASE("DBG 33 \n");LOG_FLUSH();
  if (!inForkElisionReplay) {
    addBranch();//Replayed worker already has correct number of branches from slot
  }
  
  branchesSinceLastMsg++;
  LOG_TASE("DBG 44 \n");LOG_FLUSH();
  if ( verTestType == VerTestType::REPLAY ) {
    //Replay case -- We shouldn't be here because nothing is symbolic during a replay
    LOG_TASE("ERROR: Entered forkOnPossibleIRBranches during concrete replay test \n");LOG_FLUSH();
    exit(0);
    return 0;
  } else if ( verTestType == VerTestType::TRAIN ) {
    DBG_TASE("Calling tetrinetTrainingIRFork \n");
    return tetrinetTrainingIRFork(condition);
  } else if (verTestType == VerTestType::SINGLEMSGVER || verTestType == VerTestType::VERIFY ) {
    DBG_TASE("Branching on symbolic data within IR Function \n");
    uint64_t trueBranchID  = getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true ));
    uint64_t falseBranchID = getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false));
    int isTrueChild = tase_fork_IR(trueBranchID, falseBranchID, IR_Constraint_BOWs);
    return isTrueChild;
  } else {
    LOG_TASE("ERROR: Fell through bottom case in forkOnPossibleIRBranches \n");
    std::exit(EXIT_FAILURE);
    return -1;
  }
}

int Executor::tetrinetTrainingIRFork(ref<Expr> condition) {
  if (trainType == TASETrainType::ML ) {
    ExecutionState dummy = ExecutionState(getDepCons(condition, false));
    std::vector<ref<Expr>> conditionVals = getNPossibleValues (dummy, condition, 100);
    LOG_TASE("Found %d possible symbolic branch condition values \n", conditionVals.size());fflush(stdout);
    if (conditionVals.size() != 2) {
      LOG_TASE("Sanity check failed in training IR fork: More than 2 condtion values %d \n", conditionVals.size());
      LOG_FLUSH();
      exit(1);
    }

    LOG_TASE("Found %d possible symbolic branch condition values \n", conditionVals.size());
    //Pick up here
    if (conditionVals.size() != 2) {
      LOG_TASE("Sanity check failed in training IR fork: More than 2 condtion values %d \n", conditionVals.size());
      exit(1);
    }
    ExecutionState dummyCheat = ExecutionState(getDepCons(condition, true));
    std::vector<ref<Expr>> conditionValsCheat = getNPossibleValues (dummyCheat, condition, 100);
    MOD_TASE("Found %d vals in conditionValsCheat \n", conditionValsCheat.size());
    //printNPossibleValues(dummyCheat, condition, 100);

    ref<Expr> cheatExpr = dummyCheat.constraints.getConstraintVector()[0];

    /*
      outs() << "Constraint in cheatConstraints is ";
    cheatExpr->dumpToStdout();
    outs().flush();
    */
    DBG_TASE("Found %d constraints in dummyCheat \n", dummyCheat.constraints.getConstraintVector().size());
    DBG_TASE("Found %d constraints in dummy \n", dummy.constraints.getConstraintVector().size());
    DBG_TASE("Found %d cheat constraints in dummy \n");
    bool validPathCond; //This is what the condition is after taking into account cheat constraints.

    if (onValidPath) {
      if (conditionValsCheat.size() != 1) {
	LOG_TASE("ERROR: The branch condition should be true or false after adding cheat constraints \n");
	exit(0);
      } else {
	ref<Expr> branchCond = conditionValsCheat[0];
	if (branchCond->isTrue()) {
	  validPathCond = true;
	} else if (branchCond->isFalse()) {
	  validPathCond = false;
	} else {
	  LOG_TASE("Something went wrong getting branch condition with cheat constraints \n");LOG_FLUSH();
	  worker_error(Stopped, Running);
	  exit(0);
	}
      }
    }

    if (!onValidPath || (onValidPath && !validPathCond )) {
      MOD_TASE("PID %d trying to fork off worker for true condition \n", getpid());

      //TRUE
      int trueKidPid = ::fork();
      if (trueKidPid ==0)  {
	double trueKidPidStartTime = util::getWallTime();
	onValidPath = false;
	badBranchDepth++;
	addConstraint(*GlobalExecutionStatePtr, condition);//new
	addConstraintFeature(condition);
	int currID = getNewMLID();
	dumpFeaturesTetriNET(onValidPath,  currID,  getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true)));
	if (badBranchDepth == maxBadBranchDepth) {
	  MOD_TASE("PID %d exiting  \n", getpid());
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
      MOD_TASE("PID %d trying to fork off worker for false condition \n", getpid());

      //FALSE
      int falseKidPid = ::fork();
      if (falseKidPid ==0)  {
	double falseKidPidStartTime = util::getWallTime();
	onValidPath = false;
	badBranchDepth++;
	addConstraint(*GlobalExecutionStatePtr, Expr::createIsZero(condition));//new
	addConstraintFeature(Expr::createIsZero(condition));
	int currID = getNewMLID();
	dumpFeaturesTetriNET(onValidPath,  currID,  getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false)));

	if (badBranchDepth == maxBadBranchDepth) {
	  LOG_TASE("PID %d exiting  \n", getpid());LOG_FLUSH();
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
      LOG_TASE("PID %d exiting after forking off children  \n", getpid());LOG_FLUSH();
      std::exit(EXIT_SUCCESS);
    }


    if (validPathCond) {
      addConstraint(*GlobalExecutionStatePtr,condition);
      addConstraintFeature(condition);
      int currID = getNewMLID();
      dumpFeaturesTetriNET(onValidPath, currID,getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true)));
      return 1;
    } else {
      addConstraint(*GlobalExecutionStatePtr,Expr::createIsZero(condition));
      addConstraintFeature(Expr::createIsZero(condition));
      int currID = getNewMLID();
      dumpFeaturesTetriNET(onValidPath, currID,getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false)));
      return 0;
    }
    
    //LOG_TASE("ERROR: Implement tetrinetTrainingIRFork for ML \n");
    //return -1;
  } else if (trainType == TASETrainType::CLUSTER ) {
    ref <Expr> uniqueConditionVal;
    double T0 = util::getWallTime() ;
    uniqueConditionVal = toUniquePreCalc(condition, true);
    MOD_TASE("%lf seconds elapsed in toUniquePreCalc with cheat \n", util::getWallTime() - T0);
    if  (!isa<ConstantExpr> (uniqueConditionVal)) {
      LOG_TASE("ERROR: Branch condition should be concrete after using cheat constraints \n");
      std::exit(EXIT_FAILURE);
    } 

    if (ConstantExpr * CE = dyn_cast<ConstantExpr> (uniqueConditionVal)) {
      uint64_t conditionValue = CE->getZExtValue();
      DBG_TASE("conditionValue is %lu \n", conditionValue);
      if (conditionValue == 1) {
	execution_fragment.push_back(getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(true )));
	return 1;
      } else if (conditionValue == 0) {
	execution_fragment.push_back(getMLBBIDWithIR(pre_interp_RIP, getCurrentBranchDest(false)));
	return 0;
      } else {
	LOG_TASE("ERROR:Unexpected condition value %lu \n", conditionValue);
	fflush(stdout);
	exit(0);
	return -1;
      }
      
    } else {
      LOG_TASE("ERROR: Condition value not constant expr \n");
      fflush(stdout);
      exit(0);
      return -1;
    }    
  }
}


void Executor::forkOnPossibleRIPValuesTetriNET(ref <Expr> inputExpr, uint64_t initRIP) {
  static int callCtr = 0;
  printf("Entering forkOnPossibleRIPValuesTetriNET for time %d \n", callCtr);fflush(stdout);
  callCtr++;
  branchType = 0;
  //preBranchBB = initRIP;
  //Determine if inputExpr actually has a solution given current path constraints.  Don't use
  //cheat info (e.g., keystrokes), hence the "false".
  
  printf("Attempting to call toUniquePreCalc \n");fflush(stdout);
  /*
    outs() << "Printing  expr \n";
    inputExpr->dumpToStdout();
    outs() << "Printed exp \n";
    outs().flush();
  */
  inputExpr = toUniquePreCalc(inputExpr, false);
  printf("Returned from toUniquePreCalc \n");fflush(stdout);
  if (isa<ConstantExpr> (inputExpr)) {
    printf("Only one valid value for RIP \n");
    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], inputExpr);
    return;
  }
  
  branchDepth++;
  //  mlInfo.branchesSinceLastMsg++;

  if (!inForkElisionReplay) { //Replayed worker already has correct number of branches from slot
    addBranch();
  }
  branchesSinceLastMsg++;
    
  if ( verTestType == VerTestType::REPLAY ) {
    //Replay case -- We shouldn't be here because nothing is symbolic during a replay
    printf("ERROR: Entered forkOnPossibleRIPValuesTetriNET during concrete replay test \n");fflush(stdout);
    exit(0);
  } else if ( verTestType == VerTestType::TRAIN ) {
    tetrinetTrainingFork(inputExpr, initRIP);
  } else if ( verTestType == VerTestType::SINGLEMSGVER || verTestType == VerTestType::VERIFY ) {
    ExecutionState dummy = ExecutionState(getDepCons(inputExpr, false));
    std::vector<ref<Expr>> destExprs = getNPossibleValues(dummy, inputExpr, 500);
    std::vector<uint64_t> dests;
    for (unsigned int i = 0; i < destExprs.size() ; i++) {
      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(destExprs[i])) {
	dests.push_back(CE->getZExtValue());
      } else {
	printf("Something went wrong in getNPossibleValues \n");
	exit(0);
      }
    }
    printf("DBG 1234 - dests are : \n");
    for (unsigned int i = 0; i < dests.size(); i++) {
      printf("0x%lx \n", dests[i]);
      fflush(stdout);
    }
    //int branchIdx= tase_fork(getpid(), initRIP, dests);
    
    //addConstraint(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, destExprs[branchIdx]));
    //target_ctx_gregs_OS->write(GREG_RIP*8, destExprs[branchIdx]);

    std::vector<std::vector<float>> RIP_Constraint_BOWs;
    if (klee::useLEARCHFeatsOracle) {
      RIP_Constraint_BOWs = getRIPConstraintBOWs(inputExpr, destExprs);
    }
    
    printf("Calling tase_fork_RIP \n");fflush(stdout);
    int branchIdx= tase_fork_RIP(dests,RIP_Constraint_BOWs);
    addConstraint(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, destExprs[branchIdx]));
    target_ctx_gregs_OS->write(GREG_RIP*8, destExprs[branchIdx]);
    //Pick up here
  } else {
    printf("ERROR: Fell through bottom case in forkOnPossibleRIPValues \n");fflush(stdout);
    
  }
  
}

void Executor::tetrinetTrainingFork(ref <Expr> inputExpr, uint64_t initRIP) {
  if (trainType == TASETrainType::ML ) {

    if (onValidPath) {
      LOG_TASE("PID %d entering tetrinetTrainingFork on valid path \n",getpid());LOG_FLUSH();
    } else {
      LOG_TASE("PID %d entering tetrinetTrainingFork on invalid path \n", getpid());LOG_FLUSH();
    }
    ExecutionState dummy = ExecutionState(getDepCons(inputExpr, false));
    std::vector<ref<Expr>> rips = getNPossibleValues (dummy, inputExpr, 100);
    LOG_TASE("Found %d possible symbolic RIP values without cheat constraints \n", rips.size());
    LOG_FLUSH();
    printNPossibleValues(*GlobalExecutionStatePtr, inputExpr, 100);
    ExecutionState dummyCheat = ExecutionState(getDepCons(inputExpr, true));
    std::vector<ref<Expr>> ripsCheat = getNPossibleValues (dummyCheat, inputExpr, 100);
    LOG_TASE("Found %d possible symbolic RIP values with cheat constraints \n", ripsCheat.size());LOG_FLUSH();

    ref<Expr> uniqueRIPExpr;
    if (onValidPath) {
      if (ripsCheat.size() != 1) {
	LOG_TASE("ERROR: More than 1 possible RIP Value on valid path \n");
	exit(0);
      } else {
	uniqueRIPExpr = ripsCheat[0];
      }
      //Check to make sure valid BBID is one of the destinations
      bool foundMatch = false;
      for (int i = 0; i < rips.size(); i++) {
	ConstantExpr * CE = dyn_cast<ConstantExpr> (rips[i]);
	uint64_t IP = CE->getZExtValue();
	printf("IP is 0xlx \n", IP);fflush(stdout);
	if (uniqueRIPExpr.compare(rips[i]) == 0 ) {
	  foundMatch = true;
	}
      }
      if (!foundMatch) {
	LOG_TASE("ERROR: Could not find traced RIP in list of RIPs in training fork \n");
	exit(0);
      }
    }


    for (int i = 0; i < rips.size(); i++) {
      ref<Expr> badBranchRIP;
      if (onValidPath) {
	if (uniqueRIPExpr.compare(rips[i]) == 0) {
	  LOG_TASE("Good path hit continue \n");LOG_FLUSH();
	  continue;
	}
      }
      badBranchRIP = rips[i];
      LOG_TASE("PID %d trying to fork off worker \n", getpid());LOG_FLUSH();
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
	dumpFeaturesTetriNET(onValidPath,  currID, getMLBBID(IP_Val));
	if (badBranchDepth == maxBadBranchDepth) {
	  MOD_TASE("PID %d exiting after time %lf \n", getpid(), util::getWallTime() - kidPidStartTime);
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
      LOG_TASE("PID %d exiting after forking off children after time %lf \n", getpid(), util::getWallTime() - kidPidStartTime);
      LOG_FLUSH();
      std::exit(EXIT_SUCCESS);

    }

    ref<Expr> cons = EqExpr::create(inputExpr, uniqueRIPExpr);

    addConstraint(*GlobalExecutionStatePtr, cons);//new
    addConstraintFeature(cons);
    //cons->dumpToStdout();

    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], uniqueRIPExpr);
    int currID = getNewMLID();
    ConstantExpr * CE_badBranchRIP = dyn_cast<ConstantExpr> (uniqueRIPExpr);
    uint64_t IP_Val = CE_badBranchRIP->getZExtValue();
    dumpFeaturesTetriNET(onValidPath, currID, getMLBBID(IP_Val));
    if (onValidPath) {
      LOG_TASE("Leaving training fork on valid path for time with RIP 0x%lx \n",  target_ctx_gregs[GREG_RIP].u64);LOG_FLUSH();
    }
    

    //This needs to be merged in.
    //printf("ERROR: ML training fork logic not merged in \n");fflush(stdout);
    //std::exit(EXIT_FAILURE);
    
  } else if (trainType == TASETrainType::CLUSTER ) {
    
    //Figure out valid dest using cheat info and "steer" towards that BB
    ref <Expr> uniqueRIPExpr;
    double T0 = util::getWallTime() ;
    uniqueRIPExpr = toUniquePreCalc(inputExpr, true);
    printf("Spent %lf  seconds on toUniquePreCalc with cheat \n", util::getWallTime() - T0);fflush(stdout);
    if  (!isa<ConstantExpr> (uniqueRIPExpr)) {
      printf("ERROR: RIP should be concrete after using cheat constraints \n");fflush(stdout);
      std::exit(EXIT_FAILURE);
      
    }
    ref<Expr> cons = EqExpr::create(inputExpr, uniqueRIPExpr);
    printf("Calling addConstraint from tetrinetTrainingFork \n");fflush(stdout);
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

extern std::map<uint64_t, uint64_t> tetrinetFnOffsetMap;

//This MLBBInfo stuff could be moved into a different file.
std::map<uint64_t, uint64_t> cartridge_rip_to_ID;
extern std::unordered_set<uint64_t> cartridge_heads;

void setupMLBBInfoMap() {
  LOG_TASE("Detected %lu basic block records when loading cartridge info \n", tase_num_global_records);

  for (uint32_t i = 0; i < tase_num_global_records; i++) {
    LOG_TASE("cartridge head at %x, ID: %ld\n", tase_global_records[i].head , (uint64_t) i);
    cartridge_rip_to_ID.insert({(uint64_t) tase_global_records[i].head , (uint64_t) i});
  }
}

uint64_t getMLBBIDSingleStep(uint64_t rip);

//Given the instruction pointer rip, return an ID for the basic block containing rip
// that we can use for ML purposes.  This is needed because we want the training to work
//even if the BBIDs shift slightly later because we're adding in new code (e.g. an exported
//tensorflow model) outside of the project (e.g. OpenSSL or Samba).

// RIP -> First IP in BB containing RIP -> ID
//
//Simplify the lookup.
uint64_t getMLBBID (uint64_t rip) {
  if (singleStepping) {
    return getMLBBIDSingleStep(rip);
  }
  //LOG_TASE("getMLBBID for RIP %lx\n", rip);LOG_FLUSH();

  //Get IP for first instruction in BB containing rip
  uint64_t firstIPInBB;
  uint64_t currIP = rip;
  for (int i = 0; i < 900; i++) { //This use of 900 is completely arbitrary.
    if (cartridge_heads.find(currIP) != cartridge_heads.end()) {
      auto it = cartridge_heads.find(currIP);
      firstIPInBB = *it;
      break;
    }

    if (i == 899) {
      LOG_TASE("Couldn't find first instruction in BB containing rip 0x%lx \n", rip);
      fflush(stdout);  std::exit(EXIT_FAILURE);
    }
    currIP--;
  }
  DBG_TASE("Found match for 0x%lx \n", firstIPInBB);

  
  if (clientName == "TETRINET") {
    auto it =  tetrinetFnOffsetMap.find(firstIPInBB);
    if (it != tetrinetFnOffsetMap.end()) {
      uint64_t res = it->second;
      return res;
    } else {
      LOG_TASE("Couldn't find 0x%lx in tetrinetFnOffsetMap \n",firstIPInBB);LOG_FLUSH();
      std::exit(EXIT_FAILURE);
      //worker_error(Stopped,Running);
      exit(-1);
    }
    
  }
  
  
  auto it = cartridge_rip_to_ID.find(firstIPInBB);
  if (it != cartridge_rip_to_ID.end() ) {
    //LOG_TASE("getMLBBID Debug: Returning ID %ld for IP 0x%lx \n", it->second, rip);LOG_FLUSH();
    uint64_t res = it->second;
    /*
    if (clientName == "TETRINET") {
      if (verTestType == VerTestType::SINGLEMSGVER || verTestType == VerTestType::VERIFY) {
	LOG_TASE("Doing tetrinet BB_SHIFT_CLUDGE \n");LOG_FLUSH();
	res += BB_SHIFT_CLUDGE;
      }
    }
    */
      
    return res;
  } else {
    LOG_TASE("Couldn't find ID in map for BB with first inst 0x%lx \n", firstIPInBB);LOG_FLUSH();
    std::exit(EXIT_FAILURE);
    return 0;
  }
}


//Somewhat haphazardly cobble together an identifier based on RIP of the current interpretation function
//and the number of the instruction within the interpretation function representing a branch destination.
int64_t MAX_IR_BRANCH_IDX = 65536; //2^16
uint64_t getMLBBIDWithIR(uint64_t rip, int IRBranchIdx){
  printf("Calling getMLBBIDWithIR on rip 0x%lx and IR instruction %d \n", rip, IRBranchIdx );fflush(stdout);
  
  if (IRBranchIdx > MAX_IR_BRANCH_IDX && IRBranchIdx != -1) {
    printf("ERROR: getMLBBIDWithIR called with IRBranchIdx too large \n");fflush(stdout);
    std::exit(EXIT_FAILURE);
  }
  
  uint64_t shiftedIRBranchIdx = 0;
  if (IRBranchIdx == -1) {
    printf("Regular case: Making ID for fork outside of interp fn \n");fflush(stdout);
    shiftedIRBranchIdx = 0x0000000000000000;
  } else {
    //Shift IRBranchIdx into the top 16 bits;
    //Add 1 since 0000 is a reserved value, and as far as I know, instruction 0 in the interp fn could
    //be a valid branch destination.
    IRBranchIdx = IRBranchIdx +1;
    uint64_t bigBranchIdx = (uint64_t) IRBranchIdx;
    shiftedIRBranchIdx = bigBranchIdx << 48;
    printf("Shifted IR Branch idx is 0x%lx \n", shiftedIRBranchIdx);fflush(stdout);
  }
  uint64_t BBID;
  if (singleStepping) {
    BBID = getMLBBIDSingleStep(rip);
  } else {
    BBID = getMLBBID(rip);
  }
  printf("MLBBID is 0x%lx \n", BBID);fflush(stdout);
  
  //Sanity check: Make sure top 16 bits are empty
  if ((BBID >> 48) != 0LL) {
    printf("ERROR: getMLBBIDWithIR has BBID with non empty top bits \n");fflush(stdout);
    std::exit(EXIT_FAILURE);
  }
  
  uint64_t resultID = shiftedIRBranchIdx | BBID;
  printf("End result of getMLBBIDWithIR is 0x%lx \n", resultID);fflush(stdout);
  return resultID;
  
}

//function to produce an ML ID when we're not batching instructions into cartridges (e.g., naive mode)
uint64_t getMLBBIDSingleStep(uint64_t rip){
  //We need to get a more stable ID.  For now, just return RIP...
  //It should work as long as TASE doesn't get recompiled between the
  //training and inference.
  
  return rip;
  
}


void checkMLBBIDs(std::vector<uint64_t> IDs) {
  //Sanity check to ensure that our ML basic block IDs are unique
  sort(IDs.begin(), IDs.end());
  for (unsigned int i = 0; i < IDs.size(); i++ ) {
    if (i == 0) {
      //Don't do anything.
    } else {
      if (IDs[i] == IDs[i-1]) {
	LOG_TASE("FATAL ERROR: BBID 0x%lx duplicated, %lu decimal \n", IDs[i], IDs[i]);fflush(stdout);
	exit(0);
      }
    }
  }
}


void Executor::printNPossibleValues(ExecutionState &s, ref<Expr> e, int n ) {
  printf("In printNPossibleValues \n");
  outs() << "Printing possible values for expr \n";
  int ctr = 0;
  
  std::vector<ref<Expr>> constraints = s.constraints.getConstraintVector();  //Hopefully this is just a copy
  
  while (ctr < n) {
    ctr++;
    ref<ConstantExpr> res;
    ExecutionState curr = ExecutionState(constraints);
    
    if (solver->getValue(curr, e, res)) {
      fflush(stdout);
      res->dumpToStdout();
      bool mbt;
      solver->mustBeTrue(curr, EqExpr::create(e, res), mbt);
      if (mbt) {
	printf("Solver found %d total solutions \n", ctr);
	return;
      }
      ref<Expr> neg = NotExpr::create(EqExpr::create(e, res));
      constraints.push_back(neg);
    } else {
      printf("Solver failed to find solution after %d iterations \n", ctr);
      fflush(stdout);
      return;
    }
  }
}

//Create and return new symbolic variable constrained to be any of the possible values
//at each address which offset could refer to.
ref<Expr> Executor::handleSymbolicOffset(ref<Expr> offset, const ObjectState * os, Expr::Width type) {
  //Implement me

  static int callCtr = 0;
  LOG_TASE("Entering handleSymbolicOffset for time %d \n", callCtr);LOG_FLUSH();
  callCtr++;
  std::string nameStr = "symOff_" + std::to_string(callCtr);
  //outs().flush();
  MOD_TASE("handleSymbolicOffset expr is: %s \n", offset->dumpToStr().c_str());LOG_FLUSH();
  //printf("offset expr is: \n");fflush(stdout);
  //offset->dumpToStdout();
  //outs().flush();
  ;
  ExecutionState dummy = ExecutionState(getDepCons(offset, false));
  std::vector<ref<Expr>> offs = getNPossibleValues(dummy, offset, 500);
  
  LOG_TASE("Found %ld possible symbolic offset values \n", offs.size());
  unsigned bytes = Expr::getMinBytesForWidth(type);
  LOG_TASE("operation appears to be %u bytes long \n", bytes);
  if (offs.size() == 1) {
    LOG_TASE("Special case: single offset possible.  Just use that \n");
    return os->read(offs[0], type);
  } else {
    LOG_TASE("Offset is truly symbolic \n");LOG_FLUSH();
  }
  
  void * buf = malloc(bytes + 8);
  tase_map_buf ((uint64_t) buf, bytes, "symbolicOffsetVal");
  tase_make_symbolic_internal((uint64_t) buf, (uint64_t) bytes, nameStr.c_str());
  ref<Expr> newSymVar = tase_helper_read((uint64_t) buf, (uint64_t) bytes);
  ref <Expr> allOffsetValConstraint;
  for (unsigned int i = 0; i < offs.size() ; i++) {
    
    ref<Expr> offVal = offs[i];    
    ref<Expr> val = os->read(offVal, type);
    //LOG_TASE("Symbolic offset %d is %s\n", i, val->dumpToStr().c_str());LOG_FLUSH();
    MOD_TASE("Symbolic offset    %d is %s\n", i, offVal->dumpToStr().c_str());
    MOD_TASE("Symbolic val %d is %s\n", i, val->dumpToStr().c_str());
    /*
    if (isa<ConstantExpr>(val) ) {
      ConstantExpr *CE = dyn_cast<ConstantExpr>(val) ;
      LOG_TASE("Val is 0x%lx \n",CE->getZExtValue());
    } else {
      LOG_TASE("Val isn't constant \n");
      }*/
    ref<Expr> currOffsetValConstraint = AndExpr::create(EqExpr::create(val, newSymVar), EqExpr::create(offset, offVal));    
    if (i == 0) {
      allOffsetValConstraint = currOffsetValConstraint;
    } else {
      allOffsetValConstraint = OrExpr::create(allOffsetValConstraint, currOffsetValConstraint);
    }
  }
  addConstraint(*GlobalExecutionStatePtr, allOffsetValConstraint);
  MOD_TASE("--------\n");
  return newSymVar;
  /*
  addConstraint(*GlobalExecutionStatePtr, valuesConstraint);
  printf("Trying to call toUnique\n"); fflush(stdout);
  ref<Expr> actualOffset = toUniquePreCalc(offset, true);
  printf("Called actualOffset \n");fflush(stdout);
  if (!isa<ConstantExpr>(actualOffset)) {
    printf("actualOffset isn't symbolic \n"); fflush(stdout);
    std::exit(EXIT_FAILURE);
    //deathsig(); //Todo - handle the symbolic offset even though it's a dead end for tetrinet
    //worker_exit();
  }
  ref<Expr> actualVal = os->read(actualOffset, type);
  printf("Trying to call addCheatConstraint \n");fflush(stdout);
  addCheatConstraint( EqExpr::create(newSymVar, actualVal));
  printf("Exiting handleSymbolicOffset \n"); fflush(stdout);
  return newSymVar;
  */
}

extern klee::UFElement* UF_Find(klee::UFElement*);

std::vector<ref<Expr>> Executor::getDepCons(ref <Expr> &e, bool cheat){
  std::vector<ref<Expr>> cons;
  
  //printf("Calling getDepCons \n");
  //fflush(stdout);
    
  //For each array access in the expression, add the relevant constraint groups.
  std::vector<const klee::Array * > arrays;
  klee::findSymbolicObjects(e, arrays);
  LOG_TASE("Found %d arrays referenced in expression \n", arrays.size());LOG_FLUSH();
  //printf("Found %d arrays referenced in expression \n", arrays.size());
  //fflush(stdout);
  auto it_a = arrays.begin();
  while ( it_a != arrays.end()) {
    //printf("Looping in getDepCons \n");
    //fflush(stdout);
    UFElement * rep;
    
    //Given the current array, get the union find element corresponding to it.
    if (cheat) {
      int arrayUFIdx = ufmanager_cheat->find((*it_a)->UFE_Cheat);
      rep = &((*ufmanager_cheat)[arrayUFIdx]); //Deref to get overloaded [] operator
    } else {
      int arrayUFIdx = ufmanager->find((*it_a)->UFE);
      rep = &((*ufmanager)[arrayUFIdx]);//Deref to get overloaded [] operator
    }
    /*
      if (cheat)
      ufe = const_cast<UFElement *>  (&((*it_a)->UFE_Cheat)) ;
      else
      ufe = const_cast<UFElement *>  (&((*it_a)->UFE)) ;
    */
    if (rep == NULL) {
      LOG_TASE("Error 1 in toUniquePreCalc \n");
      LOG_FLUSH();
      //worker_exit();
      std::exit(EXIT_FAILURE);
    }
    
    //printf("Found %d constraints to use \n", rep->constraints.size());
    //fflush(stdout);
    LOG_TASE("GDP DBG: rep has %d constraints \n", rep->constraints.size());LOG_FLUSH();
    cons.insert(cons.end(),rep->constraints.begin(), rep->constraints.end());
    it_a++;
    
  }
  /*
  if (taseDebug) {
    printf("Found %ld cons in getDepCons \n", cons.size());
    printf("Cons are the following: \n");
    fflush(stdout);
    auto e = cons.begin();
    while (e != cons.end()) {
      ref<Expr> ex = *e;
      ex->dumpToStdout();
      printf("-------\n");
      e++;
      fflush(stdout);
      outs().flush();
    }
    
    fflush(stdout);
  }
  */
  return cons;
}

ref<Expr> Executor::toUniquePreCalc(ref <Expr> &e, bool cheat) {
  double entry = util::getWallTime();
  std::vector<ref<Expr>> cons;
  cons = getDepCons(e, cheat);
  LOG_TASE("getDepCons took %lf seconds \n", util::getWallTime() - entry);LOG_FLUSH();
  LOG_TASE("Found %ld cons in toUniquePreCalc \n", cons.size());
  /*
  for (unsigned int i = 0; i < cons.size(); i++) {
    outs().flush();
    cons[i]->dumpToStdout();
    outs().flush();
  }
  */
  /*
  LOG_TASE("Expr is %s \n", e->dumpToStr().c_str());
  for (int i = 0; i < cons.size(); i++) {
    LOG_TASE("Constraint %d: %s \n", i, cons[i]->dumpToStr().c_str()); 
  }
  LOG_FLUSH();
  */
  ExecutionState dummy(cons);
  double T1 = util::getWallTime();
  ref <Expr> res = toUnique(dummy, e);
  LOG_TASE("toUnqiue took %lf seconds \n", util::getWallTime() - T1);LOG_FLUSH();
  
  return res;
}

void Executor::addCheatConstraint(ref <Expr> e) {
  GlobalExecutionStatePtr->addCheatConstraint(e);
}


//These NPossibleValuesCache functions are an optimization for storing past sets of values given
//an expr and set of constraints.  Both the Expr and constraints together form the key.
//Note that this is currently just implemented for 64-bit Exprs.
std::map<unsigned, std::vector<ref<klee::Expr>>> getNPossibleValuesCache; // map a hash (unsigned) for expr & constraints -> Values
void Executor::loadGetNPossibleValuesCache() {
  double T0 = util::getWallTime();
  LOG_TASE("Calling loadGetNPossibleValuesCache \n");LOG_FLUSH();
  getNPossibleValuesCache.clear();
  std::ifstream log = std::ifstream("nvaluescache");
  if (log.peek() == std::ifstream::traits_type::eof()) {
    return;
  }
  std::string line;
  
  while (std::getline(log, line)) {
    std::stringstream strm(line);
    std::vector<std::string> toks;
    std::string tmpStr;
    while(getline(strm, tmpStr, ' ')){
      toks.push_back(tmpStr);
    }
    unsigned key = (unsigned) stoul(toks[0]);
    //LOG_TASE("Found key %u load dbg \n", key);
    std::vector<ref<klee::Expr>> vals;
    for (int i = 1; i < toks.size(); i++) {
      uint64_t currVal = stoul(toks[i]);
      //LOG_TASE("Found val %llu load dbg \n", currVal);
      vals.push_back(ConstantExpr::create(currVal, Expr::Int64));
      
    }
    getNPossibleValuesCache.insert(std::make_pair(key,vals));
    
  }
  LOG_TASE("%u vals loaded for getnpossiblevaluescache load dbg\n", getNPossibleValuesCache.size());
  log.close();
  LOG_TASE("loadgetnpossible time: spent %lf seconds in printgetNPossibleValues timedbg msgCtr %d \n", util::getWallTime() -T0, msgCtr);LOG_FLUSH();
}

void Executor::printGetNPossibleValuesCache() {
  double T0 = util::getWallTime();
  DBG_TASE("Printing getNPossibleValues cache \n");
  DBG_TASE("-------\n");
  LOG_TASE("Calling printGetNPossibleValuesCache \n");LOG_FLUSH();
  FILE * cacheFile = fopen("nvaluescache", "w");
  
  for (auto it = getNPossibleValuesCache.begin(); it != getNPossibleValuesCache.end(); it++) {
    unsigned key = it->first;
    std::vector<ref<Expr>> vals = it->second;
    std::vector<ref<ConstantExpr>> constVals;
    for (int i = 0; i < vals.size(); i++) {
      if (ConstantExpr * CE = dyn_cast<ConstantExpr> (vals[i])) {
	constVals.push_back(CE);
      }else {
	LOG_TASE("FATAL ERROR in printGetNPossibleValuesCache \n");LOG_FLUSH();
	exit(1);
      }
    }
    fprintf(cacheFile, "%u", key);
    DBG_TASE("%u", key);
    for (int i = 0; i < vals.size(); i++) {
      DBG_TASE(" %llu", constVals[i]->getZExtValue());
      fprintf(cacheFile," %llu", constVals[i]->getZExtValue());
    }
    DBG_TASE("\n");
    fprintf(cacheFile,"\n");
    //fflush(cacheFile);
  }
  fflush(cacheFile);
  DBG_TASE("-------\n");
  fclose(cacheFile);
  LOG_TASE("printgetnpossible time: spent %lf seconds in printgetNPossibleValues timedbg msgCtr %d \n", util::getWallTime() -T0, msgCtr);LOG_FLUSH();
}

unsigned Executor::getExprConstraintHashKey( std::vector<ref<Expr>> constraints, ref <Expr> e) {
  unsigned hashSum = 0;
  unsigned exprHash =  e->computeHash();
  DBG_TASE("Expr dbg: expr hash %u", exprHash);
  hashSum += exprHash;
  std::vector<unsigned> constraintHashes;
  for (int i = 0; i < constraints.size(); i++) {
    constraintHashes.push_back(constraints[i]->computeHash());
    DBG_TASE("Expr dbg: constraint hash %u \n", constraints[i]->computeHash());
    hashSum += constraints[i]->computeHash();
  }
  return hashSum;
  
}

void Executor::updateGetNPossibleValuesCache(std::vector<ref<Expr>> constraints, ref <Expr> e, std::vector<ref<Expr>> vals) {
  //Todo -- sanity check to make sure key not already in map
  unsigned key = getExprConstraintHashKey(constraints, e);
  /*  std::vector<ref<ConstantExpr>> constVals;
      for (int i = 0; i < vals.size(); i++) {
      if (ConstantExpr * CE = dyn_cast<ConstantExpr> (vals[i])) {
      constVals.push_back(CE);
      }else {
      LOG_TASE("FATAL ERROR in updateGetNPossibleValuesCache \n");
      exit(1);
      }
      }*/
  DBG_TASE("Expr dbg: inserting key %u for getnpossible map ", key);
  //getNPossibleValuesCache.insert(std::make_pair(key, constVals));
  getNPossibleValuesCache.insert(std::make_pair(key, vals));
}

std::vector<ref<klee::Expr>> Executor::checkGetNPossibleValuesCache(std::vector<ref<Expr>> constraints, ref<Expr> e) {
  Expr::Width type =  e->getWidth();
  
  std::vector<ref<Expr>> results;
  if (type !=  Expr::Int64) { //Not implemented for other widths yet.
    LOG_TASE("Wrong type for cache hit \n");LOG_FLUSH();
    return results;
  }
  //LOG_TASE("Printing Expr in checkGetNPossibleValuesCache \n");
  //LOG_TASE("%s\n", e->dumpToStr().c_str());
  //LOG_TASE("Printing constraints in checkGetNPossibleValuesCache \n");LOG_FLUSH();
  for (int i = 0; i < constraints.size(); i++) {
    //LOG_TASE("Constraint %d: \n", i); LOG_FLUSH();
    //LOG_TASE("%s\n", constraints[i]->dumpToStr().c_str());
  }
  
  unsigned key = getExprConstraintHashKey(constraints, e);
  LOG_TASE("Produced key %u in checkGetNPossibleValuesCache with %d constraints \n", key, constraints.size()); LOG_FLUSH();
  auto it = getNPossibleValuesCache.find(key);
  if (it != getNPossibleValuesCache.end()) {
    results = it->second;
  }
  
  return results;
}
//This method assumes we've already trimmed out irrelevant constraints via union-find, and placed
//only relevant constraints in s.

std::vector<ref<Expr>> Executor::getNPossibleValues(ExecutionState &s, ref<Expr> e, int n, bool failOnTooBig ) {
  double entryTime = util::getWallTime();
  int ctr = 0;
  std::vector<ref<Expr>> constraints = s.constraints.getConstraintVector();  //Hopefully this is just a copy
  
  std::vector<ref<Expr>> sols;
  //LOG_TASE("getNPossibleValues: Expr is %s \n", e->dumpToStr().c_str());LOG_FLUSH();
  LOG_TASE("%d constraints in getNPossibleValues \n", constraints.size());LOG_FLUSH();
  //for (int i = 0; i < constraints.size(); i++) {
  //  LOG_TASE("constraint %d is %s \n", i, constraints[i]->dumpToStr().c_str()); LOG_FLUSH();
  //}
  double T0 = util::getWallTime();
  ConstraintManager cm(constraints);
  canonicalize(e, cm);
  constraints = cm.getConstraintVector();
  std::vector<ref<Expr>> orig_constraints = constraints;
  LOG_TASE("Canonicalizer took %lf seconds \n", util::getWallTime() - T0);LOG_FLUSH();
  sols = checkGetNPossibleValuesCache(constraints,e);
  if (sols.size() == 0) {
    LOG_TASE("getnposs dbg: Cache lookup failed \n"); LOG_FLUSH();
    
  } else {
    //LOG_TASE("getnposs dbg: cache lookup succeeded \n");
    LOG_TASE("getnposs dbg: Success - spent %lf seconds in getNPossibleValues timedbg msgCtr %d \n", util::getWallTime()-entryTime, msgCtr);LOG_FLUSH();
    LOG_TASE("cost dbg: getNPossibleValues success %lf for  msgCtr %d \n", util::getWallTime() - entryTime, msgCtr);  LOG_FLUSH();
    return sols;
  }
  
  //Add method to get IES for each array referenced in the expr E.
  while (ctr < n) {
    ctr++;
    ref<ConstantExpr> res;
    LOG_TASE("DBG 1 \n"); LOG_FLUSH();
    ExecutionState curr = ExecutionState(constraints);
    LOG_TASE("DBG 2 \n"); LOG_FLUSH();
    LOG_TASE("%d constraints in state \n", constraints.size());LOG_FLUSH();
    if (solver->getValue(curr, e, res)) {
      LOG_TASE("DBG 2.5 \n"); LOG_FLUSH();
      sols.push_back(res);
      bool mbt;
      solver->mustBeTrue(curr, EqExpr::create(e, res), mbt);
      LOG_TASE("DBG 3 \n"); LOG_FLUSH();
      if (mbt) {
	DBG_TASE("Solver found %d total solutions \n", ctr);
	LOG_TASE("Spend %lf seconds in getNPossibleValues timedbg msgCtr %d \n", util::getWallTime()-entryTime, msgCtr);LOG_FLUSH();
	LOG_TASE("cost dbg: getNPossibleValues cache miss %lf for  msgCtr %d \n", util::getWallTime() - entryTime, msgCtr);  LOG_FLUSH();
	//Add to the cache if the expr is 64 bits
	if (e->getWidth() == Expr::Int64) {
	  updateGetNPossibleValuesCache(orig_constraints, e, sols);
	}
	LOG_TASE("DBG 4 \n"); LOG_FLUSH();
	return sols;
      }
      ref<Expr> neg = NotExpr::create(EqExpr::create(e, res));
      constraints.push_back(neg);
    } else {
      LOG_TASE("Solver failed to find solution after %d iterations \n", ctr);LOG_FLUSH();
      exit(-1);
      return sols;
    }
  }
  if (failOnTooBig) {
    LOG_TASE("Found too many solutions in getNPossible solutions \n");
    std::exit(EXIT_FAILURE);
  }
  return sols;
}


int sim_piecefreq[7]; // Piece frequencies are exchanged
//before game starts.  Keep a simulated copy of these
//for the manager (since it doesn't execute through the
//client's main to populate them);

void populate_sim_piecefreq_from_str(char * s) {
  LOG_TASE("Entering populate_sim_piecefreq_from_str \n");LOG_FLUSH();
  LOG_TASE("Calling populate_sim_piecefreq_from_str on string %s \n", s);
  LOG_FLUSH();
  int i;
  //Logic from tetrinet.c
  memset(sim_piecefreq, 0, sizeof(sim_piecefreq));
  while (*s) {
    i = *s - '1';
    if (i >= 0 && i < 7)
      sim_piecefreq[i]++;
    s++;
  }
}

void populate_sim_piecefreq() {
  int loopCtr  = 0;
  LOG_TASE("DBG 1 \n");LOG_FLUSH();
  int origIdx = currTetriLogIdx;
  struct TetriNETLogRecord res = getNextTetriLogEntry();
  while (true) {
    if (res.type == S2C) {
      if (res.msg.find("newgame ") != std::string::npos) {
	break;
      }
    }
    res = getNextTetriLogEntry();
    loopCtr++;
    if (loopCtr == 10000) {
      LOG_TASE("ERROR Looping in populate_sim_piecefreq \n");LOG_FLUSH();
      exit(0);
    }
  }

  //Sample msg: We're trying to get the string of ints 1-7 (8th token after newgame)
  /*
  S2C MSG: newgame 0 1 2 1 1 1 18 1111111111111122222222222222333333333333333444444444444445555555555555566666666666666777777777777777 1111111111111111112222222222222222223334444444444446666666666666666777888888888888999999999999999999 1 1
  */
  LOG_TASE("DBG 2 \n");LOG_FLUSH();
  char * s;
  char * c_msg_str = (char *) malloc(res.msg.length() +1);
  LOG_TASE("DBG 3 \n");LOG_FLUSH();
  strcpy(c_msg_str, res.msg.c_str());
  LOG_TASE("DBG 4 \n");LOG_FLUSH();
  s = strtok(c_msg_str, " "); //newgame
  for (int i = 0; i < 8; i++) {
    s = strtok(NULL, " ");
  }
  LOG_TASE("DBG 5 \n");LOG_FLUSH();
  LOG_TASE("End str is %s \n", s);LOG_FLUSH();
  populate_sim_piecefreq_from_str(s);  
  currTetriLogIdx = origIdx;
}

int simulated_next_piece;
int simulated_random_seed = -1;
int simulated_nuklear_rand2();
void simulated_set_next_piece() {

  int n;
  //next_piece_sim = klee_new_piece();
  simulated_next_piece= -1;
  if (simulated_next_piece == -1) {
    //ABH: This seems to be the way pieces are chosen by default.
    //FILE * myLog =  fopen("abhlog.txt","w+");
    //fprintf(myLog, "Using nuklear rand to gen next piece \n");
    n = simulated_nuklear_rand2() % 100;
    simulated_next_piece = 0;
    while (n >= sim_piecefreq[simulated_next_piece] && simulated_next_piece < 6) {
      n -= sim_piecefreq[simulated_next_piece];
      simulated_next_piece++;
    }
  }
}


int simulated_nuklear_rand2() {
  simulated_random_seed = (simulated_random_seed * 1103515245) + 12345;
  return (unsigned int)(simulated_random_seed / 65536) % 32768;
  
}


void populatePieceInfo() {

  simulated_random_seed = tetrinetRandomSeed;
  LOG_TASE("Random seed seems to be %d \n", simulated_random_seed);LOG_FLUSH();
  if (simulated_random_seed == -1) {
    LOG_TASE("Error populating simulated_random_seed \n");LOG_FLUSH();
    exit(0);
  }
  populate_sim_piecefreq();
  if (msgsToVerify == -1) {
    LOG_TASE("Error: populate msgsToVerify with number of C2S partial updates to verify \n");LOG_FLUSH();
    exit(0);
  }
  for (int i= 0; i < msgsToVerify; i++) {
    simulated_set_next_piece();
    pieceIDs.push_back(simulated_next_piece);
  }
}

void printPieceInfo() {
  LOG_TASE("Printing %d piece IDs \n", pieceIDs.size());LOG_FLUSH();
  for (int i = 0; i < pieceIDs.size(); i++) {
    LOG_TASE("%d \n", pieceIDs[i]);LOG_FLUSH();
  }
}

/////////////////////////////////////////////////////////////////////////////////
//Synthetic testing (using paths discovered by LSTMs) fns below


int getBestBranchEstimate(int msg) {
  std::map<int,int>::iterator it = bestMessageBranchMap.find(msg);
  if (it != bestMessageBranchMap.end()){
    return it->second;
  } else {
    printf("ERROR getting bestBranchEstimate for msg %d \n", msg);fflush(stdout);
    std::exit(EXIT_FAILURE);
    return 0;
  }
}

//Take a given message, and the key inputs with which we'd like to produce in.  Produce
//a hacked tetrinet log with the old series of keystrokes producing message msgIdx and
//replace them with nextKeys.  This is a huge pain because the partial update C2S messages
//we have need to be "glued" with the sb and lvl messages that get sent along with the
//partial update.
std::vector<struct TetriNETLogRecord> makeTetriNETSynthLog(int msgIdx,std::vector<int> nextKeys){
  int currC2SMsgCtr = 0;
  int idxOfMsg = 0;
  for (int i = 0; i < tetriMsgLog.size() ; i++) {
    struct TetriNETLogRecord curr = tetriMsgLog[i];
    if (curr.type == puC2S) {
      if (currC2SMsgCtr == msgIdx) {
	idxOfMsg = i;
	break;
      } else {
	currC2SMsgCtr++;
      }      
    }
  }
  LOG_TASE("puC2S located at idx %d in log \n", idxOfMsg);LOG_FLUSH();

  LOG_TASE("DBG 1 \n");LOG_FLUSH();
  //Logic for getting the index at which the log messages BEFORE msgCtr and its input messages appear
  int walkBackCtr = idxOfMsg;
  int headEndIDX = -1;
  bool hasSeenINPUT = false;
  while (true) {
    walkBackCtr--;
    struct TetriNETLogRecord curr = tetriMsgLog[walkBackCtr];
    if (hasSeenINPUT) {
      if (curr.type != INPUT) {
	headEndIDX = walkBackCtr;
	LOG_TASE("headEndIDX at %d \n", headEndIDX);LOG_FLUSH();
	break;
      }
    } else {
      if (curr.type == INPUT) {
	hasSeenINPUT = true;
      }
    }
  }
  LOG_TASE("DBG 2: headEndIDX at %d \n", headEndIDX);LOG_FLUSH();
  //Make a vector of INPUT keystrokes.  The time doesn't matter because we're using it for training.
  std::vector<struct TetriNETLogRecord> middle;
  for (int i = 0; i < nextKeys.size(); i++) {
    struct TetriNETLogRecord curr;
    curr.msg = std::to_string(nextKeys[i]);
    curr.type = INPUT;
    curr.timeStamp = 0.0;
    middle.push_back(curr);
    
  }
  LOG_TASE("DBG 3 \n");LOG_FLUSH();
  //Compute the index that the puC2S (or its preceeding sb/lvl C2S messages) starts at.
  //We'll use this to make a "tail"
  walkBackCtr = idxOfMsg;
  int tailStartIDX = idxOfMsg;
  while (true) {
    walkBackCtr--;
    struct TetriNETLogRecord curr = tetriMsgLog[walkBackCtr];
    if (curr.type != INPUT) {
      tailStartIDX--;
    } else {
      LOG_TASE("tailStartIDX at %d \n", tailStartIDX); LOG_FLUSH(); 
      break;
    }
  }
  LOG_TASE("DBG 4 \n");LOG_FLUSH();
  std::vector<struct TetriNETLogRecord> tail;
  for (int i = tailStartIDX; i < tetriMsgLog.size(); i++) {
    tail.push_back(tetriMsgLog[i]);
  }
  LOG_TASE("DBG 5 \n");LOG_FLUSH();
  //Put all the pieces together
  std::vector<struct TetriNETLogRecord> result;
  
  for (int i = 0; i <= headEndIDX; i++) {
    result.push_back(tetriMsgLog[i]);
  }
  LOG_TASE("DBG 6 \n");LOG_FLUSH();
  result.insert(result.end(), middle.begin(), middle.end());
  result.insert(result.end(), tail.begin(),tail.end());
  LOG_TASE("DBG 7 \n");LOG_FLUSH();
  return result;
}

//It's easy to mess up calling this.  When we're doing verification,
//right after we verify message number msgIdx, feed this thing msgIdx.
//It will look through "trainInputExprs" for symbolic variables created
//in the last round of verification and try to produce assignments for those
//vars.


void Executor::processSyntheticPath(int msgIdx) {
  LOG_TASE("Found path with %d branches; prev estimate was %d \n", branchesSinceLastMsg, getBestBranchEstimate(msgIdx));
  std::vector<int> nextKeys;
  if ( branchesSinceLastMsg < 1) {
    LOG_TASE("Something went wrong in processSyntheticPath \n");LOG_FLUSH();
    worker_error(Stopped, Running);
    exit(0);
  }
  if ( branchesSinceLastMsg < getBestBranchEstimate(msgIdx)) {
    LOG_TASE("Second time: Found path with %d branches; prev estimate was %d \n",  branchesSinceLastMsg, getBestBranchEstimate(msgIdx));
    LOG_TASE("DBG 1 \n");LOG_FLUSH();
    updateMessageBranchMap(&bestMessageBranchMap, msgIdx, branchesSinceLastMsg);
    LOG_TASE("DBG 2 \n");LOG_FLUSH();
    //Update our known path for message msgIdx with shorter path
    LOG_TASE(" %d vals in trainInputExprs \n", trainInputExprs.size());LOG_FLUSH();
    for (int i = 0; i < trainInputExprs.size(); i++) {
      ref<Expr> currInput = trainInputExprs[i];
      ExecutionState dummy = ExecutionState(getDepCons(currInput, false));
      std::vector<ref<Expr>> vals = getNPossibleValues(dummy, currInput, 100);
      if (vals.size() != 1 ) {
	LOG_TASE("ERROR: syntheticPathTraining resulting in ambiguous keystroke \n");LOG_FLUSH();
	worker_error(Stopped, Running);
	std::exit(EXIT_FAILURE);
      }

      if (ConstantExpr *CE = dyn_cast<ConstantExpr>(vals[0])) {
	uint64_t value = CE->getZExtValue();
	LOG_TASE("Key %d is %d, %llu, %lld \n", i, (int) value, value, (int64_t) value);LOG_FLUSH();
	nextKeys.push_back((int) value);
      } else {
	LOG_TASE("ERROR: value not constant \n");LOG_FLUSH();
	worker_error(Stopped, Running);
	std::exit(EXIT_FAILURE);
      }

    }
    FILE * updatedMsgBranchMap = fopen (updatedMessageBranchMapFile.c_str(), "w+");
    printMessageBranchMap(bestMessageBranchMap, updatedMsgBranchMap); 
    std::vector<struct TetriNETLogRecord> synthLog = makeTetriNETSynthLog(msgIdx, nextKeys);    
    printTetriNETLogToFile(synthLog, updatedTetrilogFile);
    
  }
}

