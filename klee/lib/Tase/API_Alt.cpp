#include <deque>
#include <algorithm>
#include <memory>
#include <cstring>
#include <sys/prctl.h>
#include <sys/mman.h>
#include <map>
#include "API_Scout.h"
#include "klee/CommandLine.h"
#include "klee/Internal/System/Time.h"
#include "ClientWorkerFeats.h"
#include "tase_interp.h"
#include <time.h>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <stdio.h>
#include <unistd.h>
#include <dirent.h>
#include "WorkerInfo.h"
#include <sys/sem.h>
#include <iostream>
double inference_time = 0.0;
int inf_cache_hits   = 0;
int inf_cache_misses = 0;
int round_replays        =0;
double replay_time = 0.0;
extern double postInitStartTime;
double replay_start_time = 0.0;
bool curr_worker_is_replay = false;
//extern void loadGetNPossibleValuesCache();
pid_t call_fork();
extern uint64_t pre_interp_RIP;

int replay_pid = -1; //This is the pid which currently is used by the manager to schedule replays.
//Has no valid meaning in any of the worker processes.

extern FILE * prev_stdout_log;
extern uint64_t getCurrMsgTypeMavlink();
uint64_t FEATS_MAGIC_START = 0x0000DEADBEEF0000;
uint64_t FEATS_MAGIC_END = 0x0000BEEFDEAD0000;
uint64_t DINFO_MAGIC_START = 0x0000DEADBEEF0000;
uint64_t DINFO_MAGIC_END = 0x0000BEEFDEAD0000;

float CBOW_MAGIC_START = 0.1234;
float CBOW_MAGIC_END = 0.5678;



extern std::vector<WorkerInfo> new_predict_mh(struct WorkerInfo* requester, std::vector<uint64_t> dests , std::vector<void *> slots);
extern std::vector<WorkerInfo> new_predict (struct WorkerInfo* requester, std::vector<uint64_t> dests , std::vector<void *> slots, std::vector<std::vector<float>> cbows);
extern void update_mh_vector_mavlink(int cmd, int msgSize);
extern void update_mh_vector_tetrinet(float x,float y, float rot, int pieceID);
extern void update_mh_vector_tetrinet_coords(float x, float y, float rot, int pieceID);
extern uint64_t getCurrMsgTypeMavlink();
extern uint64_t getCurrMsgLenMavlink();
extern float getNthTetrinetMessageX(int n);
extern float getNthTetrinetMessageY(int n);
extern float getNthTetrinetMessageRot(int n);
extern float getNthTetrinetMessagePieceID(int n);
extern double getNthC2SPartialUpdateTime(int n);
extern std::string getNthC2SPartialUpdateAsStr(int n);
int pickedWorkers = 0;
extern int taseDebug;

namespace klee {
  extern int singleMsgVerificationIdx;
  extern bool useFallBackOracle;//Determine if we need to fall back to another oracle after a certain threshold is reached
  extern int fallBackBranchThreshold;//Fall back to the second oracle if we fail to verify in branches less than or equal to this number
  extern bool fallbackOracleActive;
  extern bool useCoordsWithoutMH;
  extern bool useLEARCHFeatsOracle;
  extern bool BBForDenseAndNoMH;
  extern bool BBForDenseAndLSTMMH;
};

int MAX_BRANCH_WIDTH = 500; //Max number of branches from a single symbolic control flow instruction
uint64_t dest_size = sizeof(uint64_t) * 600;

uint64_t cbowinfo_size = sizeof(float)*32 * 300;

uint64_t * dinfo; //Ptr into shared mem for dests and other info for fork elision
uint64_t * cbowinfo; //Ptr into shared mem which will carry constraint bag-of-words info for several branch destinations

int MAX_MLINFO_SLOTS = 10000;
void * mlinfo_cache;
void * next_open_mlinfo_slot;
extern double getCurrMsgArrTimeMavlink();

double firstMessageArrivalTime =0; //Value to normalize arrival times with

//Verification logging vectors below.  The ith value corresponds to the ith message verified.
std::vector<double> compTimes;
std::vector<double> costTimes;
std::vector<double> arrTimes;
std::vector<double> lagTimes;
std::vector<int>    roundBranches;

std::vector<double> infTimes;
std::vector<int> infCacheHits;
std::vector<int> infCacheMisses;
std::vector<int> roundReplays;
std::vector<double> roundReplayTimes;
std::vector<std::string> roundMessageTypes;
std::vector<int> roundMessageLengths;

extern int currMsgVerIdx;

extern int msgCtr;
extern int sleepDbgUs;
extern size_t MAX_RUNNING_WORKERS;
extern size_t MAX_STOPPED_WORKERS;
size_t MAX_PICKED_WORKERS = 2000;

extern std::vector<uint64_t> getExecutionFragment();
extern void load_mavlink_msgs();
extern void setupMLBBInfoMap();
void * getNewSlot();
extern uint64_t getMLBBID (uint64_t rip);
// extern void checkMLBBIDs(std::vector<uint64_t> IDs);
extern void reset_oracle_for_new_round();

extern llvm::cl::opt<bool> klee::measureTime;
extern llvm::cl::opt<int> klee::tetrinetRandomSeed;
extern "C" void renew_fds();

//Update message history vector after a round of verification
void update_mh() {
  if (klee::clientName == "MAVLINK") {
  
    int cmd = (int) getCurrMsgTypeMavlink();
    int msgSize = (int) getCurrMsgLenMavlink();
    LOG_TASE("For index %d, cmd is %d and msgSize is %d for update_mh_vector \n", currMsgVerIdx, cmd, msgSize);
    LOG_FLUSH();
    update_mh_vector_mavlink(cmd, msgSize);
  } else if (klee::clientName == "TETRINET") {
    LOG_TASE("Trying to update tetrinet message history for idx %d \n", currMsgVerIdx -1);LOG_FLUSH();
    
    float x = getNthTetrinetMessageX(currMsgVerIdx -1);
    float y = getNthTetrinetMessageY(currMsgVerIdx -1);
    float rot = getNthTetrinetMessageRot(currMsgVerIdx -1);
    //int pieceID = 0;
    int pieceID = (int) getNthTetrinetMessagePieceID(currMsgVerIdx -1);
    LOG_TASE("Updating message history with x/y/rot/piece %lf %lf %lf %d \n",x,y,rot, pieceID);LOG_FLUSH();
    if (klee::BBForDenseAndLSTMMH) {
      update_mh_vector_tetrinet_coords(x,y,rot, pieceID);
    } else {
      update_mh_vector_tetrinet(x,y,rot, pieceID);
    }
    //LOG_TASE("ERROR: Fix mh for tetrinet \n");LOG_FLUSH();
    //exit(0);
  } else {
    LOG_TASE("ERROR: Clientname not specified in update_mh \n");LOG_FLUSH();
    exit(0);
  }
}
//Force our message history (mh) to be constructed from a fixed window of previous messages.
//For example, if currMsgNum = 10 and windowSize = 5, build a mh vector from msgs 5,6,7,8,9
void setup_prev_mh_window(int currMsgNum, int windowSize) {
  //VERY IMPORTANT: Function currently assumes message history vector is already initialized to 0 prior to call.

  LOG_TASE("Entering setup_prev_mh_window for currMsgNum %d and windowSize %d \n", currMsgNum, windowSize);
  LOG_FLUSH();
  if (klee::verTestType != VerTestType::SINGLEMSGVER) {
    LOG_TASE("ERROR: Calling setup_prev_mh_window outside of single msg ver.  Add logic to wipe ml mh for full verification");
    LOG_FLUSH();
    exit(0);
  }
  
  for (int i = 0; i < windowSize; i++) {
    int idx = currMsgNum - windowSize + i;
    
    if (idx < 0)
      continue;
    else {
      LOG_TASE("Updating message history for idx %d \n", idx);LOG_FLUSH();
      float x = getNthTetrinetMessageX(idx);
      float y = getNthTetrinetMessageY(idx);
      float rot = getNthTetrinetMessageRot(idx);
      int pieceID = (int) getNthTetrinetMessagePieceID(idx);
      if (klee::BBForDenseAndLSTMMH) {
	update_mh_vector_tetrinet_coords(x, y, rot, pieceID);
      } else {
	update_mh_vector_tetrinet(x,y,rot,pieceID);
      }
    }
  }
}


//construct message history vector for msgs 0, ..., msgNum -1
void update_mh_singleMsgVerify(int msgNum) {
  LOG_TASE("Calling update_mh_singleMsgVerify on msgNum %d \n", msgNum);LOG_FLUSH();
  if (klee::clientName == "MAVLINK") {
    LOG_TASE("ERROR: implement update_mh_singleMsgVerify for mavlink \n");LOG_FLUSH();
    exit(0);
  } else if (klee::clientName == "TETRINET") {
    for (int i = 0; i < msgNum; i++) {
      float x = getNthTetrinetMessageX(i);
      LOG_TASE("DBG 11 \n");LOG_FLUSH();
      float y = getNthTetrinetMessageY(i);
      LOG_TASE("DBG 22 \n");LOG_FLUSH();
      float rot = getNthTetrinetMessageRot(i);
      LOG_TASE("DBG 33 \n");LOG_FLUSH();
      int pieceID = (int) getNthTetrinetMessagePieceID(i);
      LOG_TASE("DBG 44 \n");LOG_FLUSH();
      if (klee::BBForDenseAndLSTMMH) {
	update_mh_vector_tetrinet_coords(x, y, rot, pieceID);
      } else {
	update_mh_vector_tetrinet(x,y,rot,pieceID);
      }
    }
    
  } else {
    LOG_TASE("ERROR: Clientname not specified in update_mh_singleMsgVerify \n");LOG_FLUSH();
    exit(0);
  }
}
extern int random_seed_init;
extern void printMessageHistoryVec(FILE * log);

//Print the message history vecs for each message in the trace (except msg 0)
//and exit.  Msg N has the message history vec updated through msg N-1, and we
//print that vector and the x/y/rot/pieceID for msg N.
void calcMHVecsAndExit() {
  LOG_TASE("Entering calcMHVecsAndExit \n");LOG_FLUSH();
  FILE * mhLog = fopen("mhLog.txt", "w+");
  for (int i = 0; i < klee::msgsToVerify -1; i++) {
    float x_prev = getNthTetrinetMessageX(i);
    float y_prev = getNthTetrinetMessageY(i);
    float rot_prev = getNthTetrinetMessageRot(i);
    int pieceID_prev = (int) getNthTetrinetMessagePieceID(i);
    update_mh_vector_tetrinet(x_prev,y_prev,rot_prev,pieceID_prev);
    fprintf(mhLog, "%d,", (int) klee::tetrinetRandomSeed);
    fprintf(mhLog, "%d,", i+1);
    float x = getNthTetrinetMessageX(i+1);
    float y = getNthTetrinetMessageY(i+1);
    float rot = getNthTetrinetMessageRot(i+1);
    int pieceID = (int) getNthTetrinetMessagePieceID(i+1);    
    fprintf(mhLog,"%lf, %lf, %lf, %d,",x,y,rot,pieceID);
    printMessageHistoryVec(mhLog);
    fprintf(mhLog,"\n");
    fflush(mhLog);
  }
  exit(0);
}

std::string getCurrMsgType() {
  std::string res;
  if (klee::clientName == "MAVLINK") {
    res = std::to_string(getCurrMsgTypeMavlink());
  } else if (klee::clientName == "TETRINET") {
    std::string res = getNthC2SPartialUpdateAsStr(currMsgVerIdx);
    return res;
  } else {
    LOG_TASE("ERROR: Fix getCurrMsgType for unknown client type \n");LOG_FLUSH();
    exit(0);
  }
  return res;  
}
int getCurrMsgLen() {
  int res = -1;
  if (klee::clientName == "MAVLINK") {
    res = (int) getCurrMsgLenMavlink();
  } else if (klee::clientName == "TETRINET") {
    return res; //NA for tetrinet
  } else {
    LOG_TASE("ERROR: Fix getCurrMsgLen for unknown client type \n");LOG_FLUSH();
    exit(0);
  }
  return res;
}

double getCurrMsgArrTime() {
  if (klee::clientName == "MAVLINK") {
    return getCurrMsgArrTimeMavlink();
  } else if (klee::clientName == "TETRINET") {
    double res = getNthC2SPartialUpdateTime(currMsgVerIdx);
    LOG_TASE("Returning arrTime %lf for puC2S idx %d \n", res, currMsgVerIdx);LOG_FLUSH();
    return res;

  } else {
    LOG_TASE("ERROR: Clientname not specified in getCurrMsgArrTime \n");LOG_FLUSH();
    exit(0);
  }
}

// Send vector of something through shared mem channel w/ set size
// works in combination with receive_vec
void send_vec_dinfo(std::vector<uint64_t> * v) {

  uint64_t numItems = v->size();
  LOG_TASE("Sending %lu items in send_vec_dinfo \n", numItems);LOG_FLUSH();
  int neededSize = sizeof(DINFO_MAGIC_START) + sizeof(numItems) + numItems *sizeof(uint64_t) + sizeof(DINFO_MAGIC_END);

  if (neededSize >= dest_size ) {
    LOG_TASE("ERROR: Needed size %d greater than available bytes in dest buffer \n", neededSize);LOG_FLUSH();
    exit(0); //This should be a hard error, full-stop on the verification.
  }

  uint64_t * itrPtr = (uint64_t *) dinfo;
  *itrPtr = DINFO_MAGIC_START; itrPtr++; //For sanity check when deserializing
  *itrPtr = numItems; itrPtr++;
  for (int i = 0; i < v->size() ; i++) {
    LOG_TASE("Sending item 0x%lx \n", (*v)[i]);LOG_FLUSH();
    *itrPtr = (*v)[i]; itrPtr++;
  }
  *itrPtr = DINFO_MAGIC_END; itrPtr++;  //For sanity check when deserializing
}

std::vector<uint64_t> receive_vec_dinfo() {
  uint64_t * itrPtr = (uint64_t *) dinfo;

  //Sanity check for starting magic value...
  if (*itrPtr != DINFO_MAGIC_START) {
    LOG_TASE("ERROR: receive_vec_dinfo failed to find magic start \n");LOG_FLUSH();
    exit(0);//This should be a hard error, full-stop on the verification.
  }
  itrPtr++;
  
  std::vector<uint64_t> res;
  uint64_t numItems = *itrPtr; itrPtr++;
  LOG_TASE("Found %lu in receive_vec_dinfo items \n", numItems);LOG_FLUSH();
  for (uint64_t i = 0; i < numItems; i++) {
    LOG_TASE("Reading item 0x%lx \n", *itrPtr); LOG_FLUSH();
    res.push_back(*itrPtr); itrPtr++;
  }
  if (*itrPtr != DINFO_MAGIC_END) {
    LOG_TASE("ERROR: receive_vec_dinfo failed to find magic end and found 0x%lx \n", *itrPtr);LOG_FLUSH();
    exit(0);//This should be a hard error, full-stop on the verification.
  }
  itrPtr++;
  return res;
}

void send_cbow_feats(std::vector<std::vector<float>> * cbows) {

  int numItems = (int) cbows->size();
  LOG_TASE("Sending %lu items in send_cbow_feats \n", numItems);LOG_FLUSH();
  int neededSize = sizeof(CBOW_MAGIC_START) + sizeof(numItems) + numItems *sizeof(float)*32 + sizeof(CBOW_MAGIC_END);

  if (neededSize >= cbowinfo_size ) {
    LOG_TASE("ERROR: Needed size %d greater than available bytes in cbow serialization buffer \n", neededSize);LOG_FLUSH();
    exit(0); //This should be a hard error, full-stop on the verification.
  }

  float * itrPtr = (float *) cbowinfo;
  
  
  *itrPtr = CBOW_MAGIC_START; itrPtr++; //For sanity check when deserializing
  *itrPtr = (float) numItems; itrPtr++;

  for (int i = 0; i < numItems; i++) {
    //float currCBOW [32] = (*cbows)[i];
    //float* currCBOW = (*cbows)[i];

    std::vector<float> currCBOW = (*cbows)[i];
    
    for (int j = 0; j < currCBOW.size(); j++) {
      *itrPtr = currCBOW[j];
      itrPtr++;
    }
    
  }

  *itrPtr = CBOW_MAGIC_END; itrPtr++;  //For sanity check when deserializing  
}

std::vector<std::vector<float>> receive_cbow_feats() {
  float * itrPtr = (float *) cbowinfo;

  //Sanity check for starting magic value...
  if (*itrPtr != CBOW_MAGIC_START) {
    LOG_TASE("ERROR: receive_cbow_feats failed to find magic start \n");LOG_FLUSH();
    exit(0);//This should be a hard error, full-stop on the verification.
  }
  itrPtr++;

  std::vector<std::vector<float>> res;
  int numItems = (int) (*itrPtr);
  itrPtr++;

  for (int i = 0; i < numItems; i++) {
    //float currCons[32];
    std::vector<float> currCons;
    for (int j = 0; j < 32; j++) {
      //currCons[j] = *itrPtr;
      currCons.push_back(*itrPtr);
      itrPtr++;
    }
    res.push_back(currCons);
  }

  if (*itrPtr != CBOW_MAGIC_END) {
    LOG_TASE("ERROR: receive_cbow_feats failed to find magic end and found 0x%f \n", *itrPtr);LOG_FLUSH();
    exit(0);//This should be a hard error, full-stop on the verification.
  }
  itrPtr++;
  return res;
}


// worker_fork is intended to be called by workers
// all other items from the API are just for the managing process to call

// originator is the process that was cloned, but we use CLONE_PARENT in clone3 to reparent to the manager process
// pid/originator/branches only updated on fork. priority only set/used within manager, irrelevant for client
/*
struct WorkerInfo {
  pid_t pid;
  pid_t originator;
  size_t branches;
  double priority;
  void* pinfo; // ptr into shared memory buffer
};
*/
WorkerInfo workerInfo;

// NEW-ISH PLAN:
// Only running workers fork
//
// On fork call:
// process copies info out                                ( extern void retrieve_worker_info() )
// signal fork request to manager, process stops
// 
// manager reads info, updates predictions                ( extern void predict(WorkerInfo*) )
// manager signals go-ahead
//
// process copies info after                              ( extern void copy_worker_info() )
// then actually forks, signals the forking
// slot is recycled
// then they stop themselves
//
// new slot given when scheduled
// (which might be immediately!)


extern int pinfo_bytes; // client-defined size for pinfo struct.  **pinfo struct should have PID as the first field when stored in shared mem**

void* info_cache;
size_t cache_size;
uint64_t slots;


// client-defined items:
extern "C" {
void predict(WorkerInfo* winfo); // uses WorkerInfo items to make prediction, update priorities and info struct
void copy_worker_info(); // copy info struct into shared memory from local struct
void retrieve_worker_info(); // copy info struct from shared memory to local struct
void update_worker_info(uint64_t i); // client-specific, input is destination MBBID for next branch, should update LOCAL struct, not shared mem. Should also update PID field - this is for IPC, it is separate from the PID in WorkerInfo.
void init_oracle();
}

void sigcont_handler(int sig, siginfo_t *info, void *ucontext) {
  LOG_TASE("PID %d in sigcont_handler \n",getpid()); LOG_FLUSH();
  workerInfo.pinfo = info->si_ptr;
  //loadGetNPossibleValuesCache();
}

// size pinfo_bytes is constant per-program
// set in API user's code
void alloc_in_cache(void** pinfo) {
  
  int slot_size = pinfo_bytes % 8 == 0 ? pinfo_bytes / 8 : pinfo_bytes / 8 + 1;
  for( int x = 0; x < cache_size / (slot_size*8); x++ ) {
    if( (slots & (0x1<<x)) == 0 ) {
      slots |= (0x1<<x);
      *pinfo = (void*) (((uint8_t*) info_cache) + x*slot_size);
      return;
    }
  }
  LOG_TASE("info_cache space exceeded!\n");LOG_FLUSH();
  exit(1);
}


void dealloc_in_cache(void* pinfo) {
  DBG_TASE("Calling dealloc_in_cache on ptr 0x%lx \n", (uint64_t) pinfo);
  int slot_size = pinfo_bytes % 8 == 0 ? pinfo_bytes / 8 : pinfo_bytes / 8 + 1;
  int slot = (((uint8_t*) pinfo) - ((uint8_t*) info_cache)) / slot_size;
  slots ^= (0x1<<slot);
}

// WorkerInfo struct:
// branching information - pid, who forked it, how many branches taken, priority in queue
// program-specific info also. type-erased to void* ? ptr into shared memory allocated by API ?
// then harness can supply the type and handling code for it, and API can have
// sized requests for memory for those pointers that doesn't need compile-time info about it
//
// in trivial cases the api does nothing - calls to e.g. allocate return empty stuff;
//
// Signaling:
// default/fork -> allocation ? maybe only when put in RUNNING queue
// Abort/Error -> destruct
// Success -> printing
//
// one wrinkle: reallocation ?   NO -> static size based on # total workers allowed and a reasonable maximum struct size
// Or maybe just for RUNNING items?



// standard signal types
enum class SIGNALS {
		    ABORT,
		    SUCCESS,
		    FORK_REQUEST,
		    ERROR
};

void worker_cleanup(std::deque<WorkerInfo>& workers);

#include "WorkerGroup.h"

extern WorkerGroup * Stopped;
extern WorkerGroup * Running;
pid_t manager_pid;
int sfd;
struct signalfd_siginfo signals[MAX_EVENTS];
int num_signals;
bool success = false;
bool tase_error = false;

// void wait_started(pid_t pid) {
//   while( true ) {
//     int status;
//     waitpid(pid, &status, WUNTRACED | __WCLONE );
//     if( WIFCONTINUED(status) )
//       break;
//   }
// }


// wait could be interrupted and fail, so keep in the loop
void wait_stopped(pid_t pid) {
  while( true ) {
    int status;
    waitpid(pid, &status, WUNTRACED | __WCLONE );
    if( WIFSTOPPED(status) )
      break;
  }
}

void wait_killed(pid_t pid) {
  while( true ) {
    int status;
    waitpid(pid, &status, WUNTRACED | __WCLONE );
    if( WIFEXITED(status) || ( WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL ) )
      break;
  }
}
extern bool onValidPath;
void deathsig() {
  //Case for training
  if (!onValidPath) {
    return;
  }
  if( getpid() != manager_pid ) {
    sigval x;
    if( taseDebug ) {
      MOD_TASE("pid %d death signal.\n", getpid());
    }
    x.sival_int = static_cast<int>(SIGNALS::ABORT);
    sigqueue(manager_pid, SIGSTD, x); // abort signal to manager
    MOD_TASE("pid %d death signal.\n", getpid());
  }
}

void init_structures() {
  WorkerGroup_t type;
  if( klee::explorationType == TASEExplorationType::BFS) {
    LOG_TASE("WorkerGroup type is QUEUE \n");
    type = QUEUE;
  } else if (klee::explorationType == TASEExplorationType::DFS) {
    LOG_TASE("WorkerGroup type is STACK \n");
    type = STACK;
  } else {
    LOG_TASE("WorkerGroup type is PQ \n");
    type = PQ;
  }
  
  Stopped = new WorkerGroup(type);
  Running = new WorkerGroup(QUEUE);
  
  cache_size = MAX_RUNNING_WORKERS * pinfo_bytes;
  LOG_TASE("Initializing with %ld available workers and %ld bytes info_cache (%ld-sized slots)\n", MAX_RUNNING_WORKERS, cache_size, pinfo_bytes);LOG_FLUSH();
  
  int fd = -1;

  info_cache = mmap(NULL, cache_size, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, fd, 0);

  if( info_cache == (void*) -1 ) {
    LOG_TASE("Error during mmap\n");LOG_FLUSH();
    exit(1);
  }
  manager_pid = getpid();
  prctl(PR_SET_CHILD_SUBREAPER, 1);

  dinfo = (uint64_t*) mmap(NULL, dest_size, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, fd, 0); //For
  //destinations and other info passed between child/manager during fork request

  //Hold constraint bag-of-words info for branch destinations passed from worker to manager.
  cbowinfo = (uint64_t *) mmap(NULL, cbowinfo_size, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, fd, 0);
  
  //Slots containing WorkerMLInfo 
  mlinfo_cache = mmap(NULL, pinfo_bytes * MAX_MLINFO_SLOTS, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, fd, 0);
  next_open_mlinfo_slot = mlinfo_cache;
  
  sigset_t mask;

  sigemptyset(&mask);
  sigaddset(&mask, SIGSTD);   // standard signals

  if( sigprocmask(SIG_BLOCK, &mask, NULL) == - 1 ) {
    LOG_TASE("Could not set sigprocmask\n");LOG_FLUSH();
    exit(1);
  }

  sigemptyset(&mask);
  sigaddset(&mask, SIGSTD); // standard signals

  sfd = signalfd(-1, &mask, 0);
  if( sfd == -1 ) {
    LOG_TASE("Error creating signalfd\n");LOG_FLUSH();
    exit(1);
  }

  struct sigaction sa;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_SIGINFO; //ABH Added
  sigaddset(&sa.sa_mask, SIGCONT);
  sa.sa_sigaction = sigcont_handler;
  sigaction(SIGCONT, &sa, NULL);
  atexit(deathsig);

  setupMLBBInfoMap();

  currMsgVerIdx = (int) klee::singleMsgVerificationIdx;
  
}
/*
void init_structures(WorkerGroup ** Stopped, WorkerGroup ** Running) {
  auto type = ( klee::explorationType == TASEExplorationType::BFS || klee::explorationType == TASEExplorationType::DFS ) ? WorkerGroup_t::DEQUE : WorkerGroup_t::PQ;
  *Stopped = new WorkerGroup(type);
  *Running = new WorkerGroup(type);

  int fd = -1;
  info_cache = mmap(NULL, cache_size, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, fd, 0);

  if( info_cache == (void*) -1 ) {
    LOG_TASE("Error during mmap\n");LOG_FLUSH();
    exit(1);
  }
    
  manager_pid = getpid();
  prctl(PR_SET_CHILD_SUBREAPER, 1);
  sigset_t mask;
  sigemptyset(&mask);
  sigaddset(&mask, SIGSTD);   // standard signals

  if( sigprocmask(SIG_BLOCK, &mask, NULL) == - 1 ) {
    LOG_TASE("Could not set sigprocmask\n");LOG_FLUSH();
    exit(1);
  }

  sigemptyset(&mask);
  sigaddset(&mask, SIGSTD); // standard signals   

  sfd = signalfd(-1, &mask, 0);
  if( sfd == -1 ) {
    LOG_TASE("Error creating signalfd\n");LOG_FLUSH();
    exit(1);
  }


  struct sigaction sa;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = SA_SIGINFO; //ABH Added
  sigaddset(&sa.sa_mask, SIGCONT);
  sa.sa_sigaction = sigcont_handler;
  sigaction(SIGCONT, &sa, NULL);
  
  atexit(deathsig);
}
*/
void cleanUp() {
  LOG_TASE("Running cleanUp on Stopped \n");LOG_FLUSH();
  Stopped->cleanUp();
  LOG_TASE("Running cleanUp on Running \n");LOG_FLUSH();
  Running->cleanUp();
  LOG_TASE("Finished cleaning up \n");LOG_FLUSH();
}
bool inForkElisionReplay = false; //Are we currently replaying from an earlier process to reach a later symbolic branch?
int forkElisionReplayCtr = -1; //Number of symbolic branches we've replayed through

//At the beginning of a round of verification, worker calls this function to fork off a process as a snapshot.
//Worker then communicates the snapshot PID to the manager and continues with verification.
void workerPrepForReplay() {
  LOG_TASE("Worker %d entering workerPrepForReplay for first time in round \n", getpid());LOG_FLUSH();
  int plzDontForkBomb = 2000;
  if (plzDontForkBomb == 0) {
    LOG_TASE("Max number of replay pids reached.  If you don't think the path prediction logic is broken, increase the limit \n");LOG_FLUSH();
  }
  while (plzDontForkBomb >= 0) {//Replace with while(true) when you're feeling bold
    plzDontForkBomb--;
    LOG_TASE("plzDontForkBomb is %d \n", plzDontForkBomb);LOG_FLUSH();
    int pid = call_fork();
    if (pid == 0) {
      kill(getpid(), SIGSTOP);
      //REPLAY ENTRY POINT IS HERE
      LOG_TASE("pid %d about to get worker info for replay \n");LOG_FLUSH();
      retrieve_worker_info(); //Get the juicy details for our replay
      LOG_TASE("pid %d starting replay with frag size %d \n",getpid() ,getExecutionFragment().size());LOG_FLUSH();
      inForkElisionReplay = true;
      forkElisionReplayCtr = 0;
    } else {      
      std::vector<uint64_t> pidVec;
      pidVec.push_back((uint64_t) pid);
      send_vec_dinfo(&pidVec);
      kill(getpid(), SIGSTOP);
      LOG_TASE("PID %d running again after prepping a replay pid %d \n", getpid(), pid);LOG_FLUSH();
      break;
    }
    
  }
}

//Wait for parent to stop and get the replay pid.
//Called by manager
int managerPrepForReplay(WorkerInfo parent) {
  // wait_stopped(parent.pid);
  LOG_TASE("MANAGER entering managerPrepforReplay \n");LOG_FLUSH();
  std::vector<uint64_t> replayPIDVec = receive_vec_dinfo();
  if (replayPIDVec.size() != 1) {
    LOG_TASE("ERROR: Seems to be more than one replay PID.  Doesn't make sense. \n");LOG_FLUSH();
    exit(0);
  }
  int res = (int) replayPIDVec[0];
  LOG_TASE("MANAGER about to start waiting on new replay pid %d \n", res);LOG_FLUSH();
  wait_stopped(res);
  return res;
  //sigval x;
  //x.sival_ptr = parent.pinfo
  //sigqueue(parent.pid, SIGCONT, x);
}

//Suppose "w" represents a branch which requires a replay to explore.  Assign "w"
//to our current replay pid (created at the beginning of the round), and update
//replay_pid to a new replay process, since "w" consumes the old replay process.
//Called by manager.
int setup_for_replay(WorkerInfo w) {
  //Sanity check
  if (w.pid != -1) {
    LOG_TASE("Attempting to replay with preexisting pid %d \n", w.pid); LOG_FLUSH();
    exit(0);
  }
  if (replay_pid <= 0) {
    LOG_TASE("ERROR: Invalid replay pid \n");LOG_FLUSH();
    exit(0);
  }
  
  int res = replay_pid; //Assign the current replay pid to w
  
  sigval x;
  x.sival_ptr = w.pinfo; //This pointer has all the info needed for a replay
  LOG_TASE("setup_for_replay: Manager about to SIGCONT  %d \n", res); LOG_FLUSH();
  sigqueue(res, SIGCONT, x);

  LOG_TASE("setup_for_replay: Manager about to wait on %d \n", res);  LOG_FLUSH();
  wait_stopped(res);// Wait for replay_pid to fork a new replay process, and send us its ID.
  std::vector<uint64_t> replayPIDVec =receive_vec_dinfo();
  if (replayPIDVec.size() != 1) {
    LOG_TASE("ERROR: Seems to be more than one replay PID.  Doesn't make sense. \n");LOG_FLUSH();
    exit(0);
  }
  
  replay_pid = (int) replayPIDVec[0];
  LOG_TASE("New replay_pid from setup_for_replay is %d \n", replay_pid);LOG_FLUSH();
  wait_stopped(replay_pid);
  LOG_TASE("Manager wait_stopped completed on pid %d \n", replay_pid);LOG_FLUSH();
  //sigqueue(res, SIGCONT, x);
  return res;
}

//

void resetSlots();
void resetForBackupOracle() {
  LOG_TASE("Running resetForBackupOracle \n");LOG_FLUSH();

  //Purge stopped queue.  We're assuming running is empty at this point.
  Stopped->cleanUp();
  LOG_TASE("Running resetForBackupOracle DBG1 \n");LOG_FLUSH();
  //Reset bump allocator for slots
  resetSlots();
  LOG_TASE("Running resetForBackupOracle DBG2 \n");LOG_FLUSH();
  void * slot = getNewSlot();
  LOG_TASE("Running resetForBackupOracle DBG3 \n");LOG_FLUSH();
  //Pick up here PUH
  memset(slot, 0, pinfo_bytes);
  LOG_TASE("Running resetForBackupOracle DBG4 \n");LOG_FLUSH();
  WorkerInfo w {-1,-1, 0, -1, slot};
  LOG_TASE("Running resetForBackupOracle DBG5 \n");LOG_FLUSH();
  int assigned_pid = setup_for_replay(w);
  w.pid = assigned_pid;
  LOG_TASE("Running resetForBackupOracle DBG6 \n");LOG_FLUSH();
  Stopped->push(w);
  LOG_TASE("Running resetForBackupOracle DBG7 \n");LOG_FLUSH();
  //Move the replay PID into stopped, and make it fork off another replay PID for later
  //WorkerInfo w{pid, getpid(), 0, -1, getNewSlot()};
  
  
}

//NEW
int schedule_worker() {
  if ( Running->size() < MAX_RUNNING_WORKERS ) {
    //PUH
    LOG_TASE("Running schedule_worker \n");LOG_FLUSH();
    
    if (klee::useFallBackOracle && !klee::fallbackOracleActive && pickedWorkers >= klee::fallBackBranchThreshold) {
      //Purge stopped (running should be empty) and place our replay process (taken at beginning of round) in running
      klee::fallbackOracleActive = true;
      resetForBackupOracle();
      pickedWorkers++;
      //return 1;
    }
    LOG_TASE("Running schedule_worker DBG 1 \n");LOG_FLUSH();
    
    WorkerInfo curr = Stopped->pop();
    //alloc_in_cache(&curr.pinfo); //Now handled with slots
    pickedWorkers++;

    if (curr.pid == -1) {
      //LOG_TASE("ERROR in schedule_worker.  Need to implement replay \n");LOG_FLUSH();
      //exit(0);
      curr_worker_is_replay = true;
      round_replays++;
      replay_start_time = klee::util::getWallTime();
      int assigned_pid = setup_for_replay(curr);
      LOG_TASE("ATTEMPTING REPLAY with pid %d  \n", assigned_pid);LOG_FLUSH();
      curr.pid = assigned_pid;
    }
    Running->push(curr);
    LOG_TASE("Manager scheduling pid %d, from parent pid: %d. Priority %lf \n", curr.pid, curr.originator, curr.priority);LOG_FLUSH();
    sigval x;
    x.sival_ptr = curr.pinfo;
    sigqueue(curr.pid, SIGCONT, x);
    return 1;
  }
  return 0;
}

// fork replacement but with reparenting to calling process's parent to allow manager to wait
pid_t call_fork() {
  struct clone_args args = {};
  args.flags = CLONE_PARENT;
  double T0 = klee::util::getWallTime();
  pid_t res = (pid_t) syscall(SYS_clone3, &args, sizeof(struct clone_args));
  if (res != 0) {
    LOG_TASE("cost dbg: fork time %lf for  msgCtr %d \n", klee::util::getWallTime() - T0, msgCtr);
  }
  LOG_TASE("Fork DBG: seconds/idx are |%lf|%d|%d \n", klee::util::getWallTime() - T0, currMsgVerIdx,msgCtr);LOG_FLUSH();
  return res;
}

//Does anything call this now that we have the PQ version?
//TODO: Rip it out
pid_t worker_fork(WorkerGroup * Stopped, WorkerGroup * Running) {
  LOG_TASE("ERROR: Remove references to worker fork with calls to tase_fork \n");LOG_FLUSH();
  exit(0);
  
  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
  sigqueue(manager_pid, SIGSTD, x);

  kill(getpid(), SIGSTOP);
  
  pid_t child;
  double startTime, endTime;
  if( klee::measureTime ) {
    startTime = klee::util::getWallTime();
    child = call_fork();
    endTime = klee::util::getWallTime();
  } else {
    child = call_fork();
  }
  if( child == -1 ) {
    LOG_TASE("Fork failed\n");LOG_FLUSH();
    worker_error(Stopped, Running);
    exit(1);
  }
  if( child != 0 ) { // parent worker -> signal manager
    if( klee::measureTime ) {
      LOG_TASE("fork syscall took %lf seconds. \n", endTime - startTime);LOG_FLUSH();
    }
    x.sival_int = *reinterpret_cast<int*>(&child);  // pid_t isn't int but same size/signedness
    sigqueue(manager_pid, SIGSTD, x);
  } else {
    cycleTASELogs(false);
    renew_fds();
    kill(getpid(), SIGSTOP);
  }

  return child;
}


pid_t initial_fork() {
  struct clone_args args = {};
  MOD_TASE("PID %d Calling initial_fork \n", getpid());
  pid_t pid = (pid_t) syscall(SYS_clone3, &args, sizeof(struct clone_args));


  if( pid == -1 ) {
    LOG_TASE("Fork failed\n");LOG_FLUSH();
    cleanUp();
    //destroy_structures(&Stopped, &Running);
    exit(1);
  }

  if( pid != 0 ) {
    LOG_TASE("Parent pushing into Stopped\n");LOG_FLUSH();
    WorkerInfo w{pid, getpid(), 0, -1, getNewSlot()};
    //Stopped->push(WorkerInfo{pid, getpid(), 0, -1, getNewSlot()});
    Stopped->push(w);
    LOG_TASE("Parent calling wait_stopped\n");LOG_FLUSH();
    wait_stopped(pid);
    replay_pid = managerPrepForReplay(w);
    LOG_TASE("finished waiting\n");LOG_FLUSH();
    
  } else {
    //LOG_TASE("Worker %d trying to sigstop self in initial_fork \n", getpid());LOG_FLUSH();
    //kill(getpid(), SIGSTOP);
    workerPrepForReplay();
    LOG_TASE("Worker %d running again after sigstop \n", getpid());LOG_FLUSH();
  }

  return pid;
}

// WorkerMLInfo getWorkerMLInfo (int pid) {
//   auto lookup = MLInfoMap.find(pid);
//   if (lookup == MLInfoMap.end()) {
//     printf("FATAL ERROR: couldn't return MLInfo for pid %d \n", pid); fflush(stdout);
//     exit(1);
//   }
//   WorkerMLInfo res = lookup->second;
//   return res;
// }

//extern std::vector<uint8_t> getCurrMsgToVerifyMavlink();

// implement in client-specific code
// extern std::vector<uint8_t> getCurrMsgToVerifyMavlink();
// std::vector<uint8_t> getCurrMsgToVerify() {
// #ifdef TASE_TETRINET
//   return getCurrMsgToVerifyTetriNET();
// #elif defined(TASE_MAVLINK)
//   return getCurrMsgToVerifyMavlink();
// #else
//   std::vector<uint8_t> dummyRes;
//   printf("ERROR: Need to implement client specific logic in getCurrMsgToVerify \n");fflush(stdout);
//   exit(0);
//   return dummyRes;
// #endif
// }


void resetSlots() {
  next_open_mlinfo_slot = mlinfo_cache;
}

void * getNewSlot() {
  void * res = next_open_mlinfo_slot;

  next_open_mlinfo_slot =(void *)( (uint64_t) next_open_mlinfo_slot + (uint64_t) pinfo_bytes);

  //Make sure we don't run out of space:
  if ((uint64_t)next_open_mlinfo_slot >= ((uint64_t) mlinfo_cache) + MAX_MLINFO_SLOTS * pinfo_bytes) {
    LOG_TASE("ERROR: Out of space in mlinfo_cache \n");LOG_FLUSH();
    //De-duplicate later
    if (klee::printRecordsOnVerFail == true) {

      //Populates stats for this weird failure case so we at least have some records.  De-duplicate me later.
      double costTime = klee::util::getWallTime() - postInitStartTime;
      costTimes.push_back(costTime);
      postInitStartTime = klee::util::getWallTime();

      double arrTime = getCurrMsgArrTime();
      if (msgCtr == 0) {
	firstMessageArrivalTime = arrTime; //Normalize message arrival times so that first msg comes at time 0
      }
      arrTime = arrTime - firstMessageArrivalTime;

      roundMessageTypes.push_back(getCurrMsgType());
      roundMessageLengths.push_back(getCurrMsgLen());

      arrTimes.push_back(arrTime);
      double compTime;
      if (msgCtr == 0) {
	compTime = costTime;
      } else {
	compTime = std::max(arrTimes[msgCtr], compTimes[msgCtr-1]) + costTimes[msgCtr];
      }
      compTimes.push_back(compTime);
      lagTimes.push_back(compTimes[msgCtr] - arrTimes[msgCtr]);
      roundBranches.push_back(pickedWorkers);
      infTimes.push_back(inference_time);
      infCacheHits.push_back(inf_cache_hits);
      infCacheMisses.push_back(inf_cache_misses);
      roundReplays.push_back(round_replays);
      roundReplayTimes.push_back(replay_time);


      //Todo: De-duplicate this with the other printing we do for LOG_RECORDs
      if (klee::clientName == "MAVLINK" ) {
	LOG_TASE("LOG_RECORD_FIELDS: ,RUN,MSGIDX,ARR,COST,LAG,BRANCHES,REPLAYS,REPLAYTIME,INFTIME,INFCACHEHITS,INFCACHEMISSES,MSGTYPE,MSGLEN,ELISION_THRESHOLD,ID_STR\n");
	for (int i = 0; i < lagTimes.size(); i++) {
	  LOG_TASE("LOG_RECORD: ,%d,%d,%lf,%lf,%lf,%d,%d,%lf,%lf,%d,%d,%s,%d,%lf,%s\n", (int) klee::mavlinkTraceNum, i,arrTimes[i],costTimes[i], lagTimes[i],roundBranches[i],roundReplays[i],roundReplayTimes[i],infTimes[i],infCacheHits[i], infCacheMisses[i], roundMessageTypes[i].c_str(), roundMessageLengths[i], (double)klee::forkElisionPriorityThreshold, (std::string) klee::logIDStringArg);LOG_FLUSH();
	}
      } else if (klee::clientName == "TETRINET") {
	for (int i = 0; i < lagTimes.size(); i++) {
	  LOG_TASE("LOG_RECORD: ,%d,%d,%lf,%lf,%lf,%d,%d,%lf,%lf,%d,%d,%lf,%s\n", (int) klee::tetrinetRandomSeed, i,arrTimes[i],costTimes[i], lagTimes[i],roundBranches[i],roundReplays[i],roundReplayTimes[i],infTimes[i],infCacheHits[i],infCacheMisses[i],(double)klee::forkElisionPriorityThreshold,((std::string) klee::logIDStringArg).c_str());LOG_FLUSH();
	}
      }



    }





    exit(0);
  }
  return res;
  
}

std::vector<void *> getNewSlots(int size) {
  std::vector<void *> res;
  for (int i = 0; i < size; i++) {
    res.push_back(getNewSlot());
  }
  return res;
}

void fetch_signals() {
  int bytes = read( sfd, signals, sizeof(struct signalfd_siginfo) * MAX_EVENTS );
  if ( bytes == 0 ) {
    num_signals = 0;
    return;
  } else if ( bytes == -1 ) {
    LOG_TASE("Error reading events\n");LOG_FLUSH();
    cleanUp();
    //destroy_structures(&Stopped, &Running);
    exit(1);
  }

  num_signals = bytes / sizeof(struct signalfd_siginfo);
}

void clear_signals() {
  memset(&signals[0], '\0', MAX_EVENTS*sizeof(struct signalfd_siginfo));
}

extern "C" uint64_t getWorkerLastMLBBID(WorkerInfo w);
bool compareWorkerPriorityDescending(WorkerInfo& w1, WorkerInfo& w2) {
  return w1.priority > w2.priority;
}

//double priorityThreshold = .95;

//Return a vector of branches worthy of being backed with a process, so that
//when the branch is explored later, we don't have to replay from an earlier point
//in time.  Ordered from most to least attractive so that the first branch is
//assigned to the parent pid which encountered the branch.
std::vector <uint64_t> choose_branches_to_elide(std::vector<WorkerInfo> candidates) {
  
  std::vector<uint64_t> res;
  //Sort our candidates by priority (decreasing) first.
  std::sort(candidates.begin(), candidates.end(), compareWorkerPriorityDescending);
  
  //Always assign parent to best branch (first candidate), even if less than threshold
  res.push_back(getWorkerLastMLBBID(candidates[0]));
  LOG_TASE("Returning best branch ID %lu with priority %lf \n", getWorkerLastMLBBID(candidates[0]), candidates[0].priority);
  LOG_FLUSH();
  for (int i = 1; i < candidates.size(); i++) {
    uint64_t branchID = getWorkerLastMLBBID(candidates[i]);
    LOG_TASE("Returning branch ID %lu with priority %lf \n", branchID, candidates[i].priority);LOG_FLUSH();
    if (candidates[i].priority >= klee::forkElisionPriorityThreshold) {
      res.push_back(branchID);
    } else {
      //Don't include the branch
    }
  }
  return res;
}

//NEW
// where the magic happens
void handle_signals() {
  LOG_TASE("Entering handle_signals \n");LOG_FLUSH();
  fetch_signals();
  for( int i = 0; i < num_signals; i++ ) {
    WorkerInfo tmp;
    sigval x;

    if( signals[i].ssi_signo == SIGSTD ) { // standard signals
      switch( SIGNALS(signals[i].ssi_int) ) {
      case SIGNALS::ERROR:
	if (curr_worker_is_replay) {
	  replay_time += klee::util::getWallTime() - replay_start_time;
	  curr_worker_is_replay = false;
	}
	LOG_TASE("Encountered ERROR signal.  Manager shutting down \n"); 
	cleanUp();
	exit(1);
      case SIGNALS::ABORT:
	if (curr_worker_is_replay) {
	  replay_time += klee::util::getWallTime() - replay_start_time;
	  curr_worker_is_replay = false;
	}
	Running->get(&tmp, signals[i].ssi_pid);

	MOD_TASE("Signal: Abort, pid %d\n", signals[i].ssi_pid); 
	//dealloc_in_cache(tmp.pinfo);
	MOD_TASE("manager trying to wait on pid %d \n", signals[i].ssi_pid); 
	wait_killed(signals[i].ssi_pid);
	MOD_TASE("manager finished waiting \n"); 
	break;

      case SIGNALS::SUCCESS: // print something here...
	LOG_TASE("Signal: Success, pid %d\n", signals[i].ssi_pid); LOG_FLUSH();
	if (curr_worker_is_replay) {
	  replay_time += klee::util::getWallTime() - replay_start_time;
	  curr_worker_is_replay = false;
	}
	
	//currMsgVerIdx++;
	if ( klee::verTestType == VerTestType::TRAIN || klee::verTestType == VerTestType::REPLAY || klee::verTestType == VerTestType::SINGLEMSGVER ) {
	  success = true;
	  double runTime = klee::util::getWallTime() - postInitStartTime;
	  LOG_TASE("SUCCESS in worker for msg idx |%d|%lf|%d \n", (int) klee::singleMsgVerificationIdx, runTime, pickedWorkers); LOG_FLUSH();
	  if (klee::clientName == "MAVLINK" ) {
	    LOG_TASE("MSG %d SUCCESSFULLY VERIFIED in %lf seconds with %d branches explored and msg type %d \n",(int) klee::singleMsgVerificationIdx, runTime, pickedWorkers, getCurrMsgTypeMavlink());LOG_FLUSH();
	  } else {
	    LOG_TASE("MSG %d SUCCESSFULLY VERIFIED in %lf seconds with %d branches explored  \n",(int) klee::singleMsgVerificationIdx, runTime, pickedWorkers);LOG_FLUSH();
	  }
	  LOG_TASE("Manager exiting \n");LOG_FLUSH(); 	  
	  cleanUp();
	  exit(0);
	} else if (klee::verTestType == VerTestType::VERIFY) {
	  double costTime = klee::util::getWallTime() - postInitStartTime;
	  costTimes.push_back(costTime);
	  postInitStartTime = klee::util::getWallTime();

	  double arrTime = getCurrMsgArrTime();
	  if (msgCtr == 0) {
	    firstMessageArrivalTime = arrTime; //Normalize message arrival times so that first msg comes at time 0
	  }
	  arrTime = arrTime - firstMessageArrivalTime;

	  roundMessageTypes.push_back(getCurrMsgType());
	  roundMessageLengths.push_back(getCurrMsgLen());
	  
	  arrTimes.push_back(arrTime);
	  double compTime; 
	  if (msgCtr == 0) {
	    compTime = costTime;
	  } else {
	    compTime = std::max(arrTimes[msgCtr], compTimes[msgCtr-1]) + costTimes[msgCtr];
	  }
	  compTimes.push_back(compTime);
	  lagTimes.push_back(compTimes[msgCtr] - arrTimes[msgCtr]);
	  roundBranches.push_back(pickedWorkers);
	  infTimes.push_back(inference_time);
	  infCacheHits.push_back(inf_cache_hits);
	  infCacheMisses.push_back(inf_cache_misses);
	  roundReplays.push_back(round_replays);
	  roundReplayTimes.push_back(replay_time);
	  LOG_TASE("SUCCESS in worker for msg idx |%d|%lf|%d \n", msgCtr, costTime, pickedWorkers);LOG_FLUSH();
	  msgCtr++;
	  curr_worker_is_replay = false;
	  inf_cache_hits = 0;
	  inf_cache_misses = 0;
	  inference_time = 0;
	  round_replays = 0;
	  replay_time = 0;
	  pickedWorkers = 0;
	  klee::fallbackOracleActive = false; //Swap back to primary oracle.
	  //kill lingering workers from current round
	  LOG_TASE("Killing workers leftover from current round \n");LOG_FLUSH();
	  double start = klee::util::getWallTime();
	  Stopped->cleanUp();
	  LOG_TASE("Killing done in %lf seconds \n", klee::util::getWallTime() - start);LOG_FLUSH();

	  if (klee::msgsToVerify <= 0) {
	    LOG_TASE("ERROR: Populate msgsToVerify \n");LOG_FLUSH();
	    exit(0);
	  }
	  if (msgCtr >= klee::msgsToVerify) {
	    LOG_TASE("Manager verified all messages \n");LOG_FLUSH();
	    if (klee::clientName == "MAVLINK" ) {
	      LOG_TASE("LOG_RECORD_FIELDS: ,RUN,MSGIDX,ARR,COST,LAG,BRANCHES,REPLAYS,REPLAYTIME,INFTIME,INFCACHEHITS,INFCACHEMISSES,MSGTYPE,MSGLEN,ELISION_THRESHOLD,ID_STR\n");
	      for (int i = 0; i < lagTimes.size(); i++) {
		LOG_TASE("LOG_RECORD: ,%d,%d,%lf,%lf,%lf,%d,%d,%lf,%lf,%d,%d,%s,%d,%lf,%s\n", (int) klee::mavlinkTraceNum, i,arrTimes[i],costTimes[i], lagTimes[i],roundBranches[i],roundReplays[i],roundReplayTimes[i],infTimes[i],infCacheHits[i], infCacheMisses[i], roundMessageTypes[i].c_str(), roundMessageLengths[i], (double)klee::forkElisionPriorityThreshold, (std::string) klee::logIDStringArg);LOG_FLUSH();
	      }
	    } else if (klee::clientName == "TETRINET") {
	      for (int i = 0; i < lagTimes.size(); i++) {
		LOG_TASE("LOG_RECORD: ,%d,%d,%lf,%lf,%lf,%d,%d,%lf,%lf,%d,%d,%lf,%s\n", (int) klee::tetrinetRandomSeed, i,arrTimes[i],costTimes[i], lagTimes[i],roundBranches[i],roundReplays[i],roundReplayTimes[i],infTimes[i],infCacheHits[i],infCacheMisses[i],(double)klee::forkElisionPriorityThreshold,((std::string) klee::logIDStringArg).c_str());LOG_FLUSH();
	      }
	    }
	    exit(0);
	  }

	  //Reset bump allocator for slots
	  resetSlots();
	  //Kill replay pid from last round
	  kill(replay_pid, SIGKILL);
	  replay_pid = -1;

	  Running->get(&tmp, signals[i].ssi_pid);
	  //Make sure we update msg ctr
	  LOG_TASE("About to wait on %d for replay setup \n", tmp.pid);LOG_FLUSH();
	  wait_stopped(tmp.pid);
	  LOG_TASE("Waited \n"); LOG_FLUSH();
	  replay_pid = managerPrepForReplay(tmp);
	  LOG_TASE("replay_pid is now %d \n", replay_pid);LOG_FLUSH();
	  //Wait, and then start another round of verification
	  //Running->get(&tmp, signals[i].ssi_pid);
	  if (sleepDbgUs != 0 ) {
	    LOG_TASE("Manager sleeping for %d microseconds \n",  sleepDbgUs);LOG_FLUSH();
	    usleep((sleepDbgUs));
	  }
	  //wait_stopped(tmp.pid);
	  tmp.pinfo = getNewSlot();  //Make sure worker is using new slot
	  LOG_TASE("Done waiting on process  \n");LOG_FLUSH();	  
	  //dealloc_in_cache(tmp.pinfo);
	  Stopped->push(tmp);

	  currMsgVerIdx++;
	  reset_oracle_for_new_round();
	  
	  double T1 = klee::util::getWallTime();
	  if (klee::useMLMH) {
	    update_mh();
	  }
	  inference_time += klee::util::getWallTime() -T1;
	}
	
	return; // ignore remaining signals

      case SIGNALS::FORK_REQUEST:
	{
	  if (curr_worker_is_replay) {
	    replay_time += klee::util::getWallTime() - replay_start_time;
	    curr_worker_is_replay = false;
	  }
	  
	  double T0 = klee::util::getWallTime();
	  LOG_TASE("MANAGER in fork_request case \n");
	  Running->find(&tmp, signals[i].ssi_pid);
	  
	  LOG_TASE("Trying to call wait_stopped on pid %d \n", tmp.pid);LOG_FLUSH();

	  wait_stopped(tmp.pid); // make sure parent has time to set pid of child in pinfo
	  x.sival_ptr = tmp.pinfo;
	  kill(tmp.pid, SIGCONT);
	  
	  wait_stopped(tmp.pid);
	  LOG_TASE("FR DBG 1 %lf \n", klee::util::getWallTime() - T0);LOG_FLUSH();
	  std::vector<uint64_t> dests = receive_vec_dinfo();
	  LOG_TASE("FR DBG 2 %lf \n", klee::util::getWallTime() - T0);LOG_FLUSH();
	  LOG_TASE("%ld destinations recieved\n", dests.size()); LOG_FLUSH();

	  std::vector<std::vector<float>> cbows;
	  if (klee::useLEARCHFeatsOracle) {
	    LOG_TASE("Calling receive_cbow_feats \n");LOG_FLUSH();
	    cbows = receive_cbow_feats();
	    LOG_TASE("Called receive_cbow_feats \n");LOG_FLUSH();
	  }
	  //Fork requester has called copy_worker_info to populate mlinfo prior to branches
	  //into manager's mlInfo

	  std::vector <WorkerInfo> candidates;
	  //for (int i = 0; i < dests.size(); i++) {
	  LOG_TASE("AH DBG 1 \n");LOG_FLUSH();
	  std::vector<void *> slots = getNewSlots(dests.size());
	  LOG_TASE("AH DBG 2 \n");LOG_FLUSH();
	  double start = klee::util::getWallTime();
	  LOG_TASE("AH DBG 3 \n");LOG_FLUSH();
	  //heeeere
	  if (klee::verTestType == VerTestType::SINGLEMSGVER) {
	    msgCtr = klee::singleMsgVerificationIdx;
	  }
	  if (klee::useMLMH || klee::useCoordsWithoutMH ||klee::BBForDenseAndNoMH) {
	    LOG_TASE("AH DBG 4 \n");LOG_FLUSH();
	    candidates = new_predict_mh(&tmp, dests, slots);
	  } else {
	    LOG_TASE("AH DBG 5 \n");LOG_FLUSH();
	    LOG_TASE("%d and %d vals in dests and slots \n", dests.size(), slots.size());LOG_FLUSH();
	    for (int i = 0; i < slots.size(); i++) {
	      LOG_TASE("0x%lx for slot %d \n", (uint64_t) slots[i], i);LOG_FLUSH();
	    }
	    candidates = new_predict(&tmp, dests, slots, cbows);
	  }
	  
	  //for (int i = 0; i < candidates.size(); i++) {
	  //  LOG_TASE("Candidate %d  has priority %lf and BBID %d \n"
	  //}
	  
	  inference_time += klee::util::getWallTime() - start;
	  LOG_TASE("FR DBG 3 %lf \n", klee::util::getWallTime() - T0);LOG_FLUSH();
	  // }
	  //Sanity check
	  for (int i = 0; i < dests.size(); i++) {
	    LOG_TASE("Candidate %d has priority %lf \n", i, candidates[i].priority);LOG_FLUSH();
	    if (klee::explorationType != TASEExplorationType::BFS) {
	      if (candidates[i].priority < 0) {
		LOG_TASE("ERROR populating candidate with priority %lf \n", candidates[i].priority);LOG_FLUSH();
		exit(0);
	      }
	    }
	  }
	  
	  std::vector <uint64_t> chosen = choose_branches_to_elide(candidates); 
	  
	  send_vec_dinfo(&chosen);

	  x.sival_ptr = tmp.pinfo;
	  sigqueue(tmp.pid, SIGCONT, x);

	  MOD_TASE("Calling wait_stopped on pid %d\n", tmp.pid);LOG_FLUSH();
	  wait_stopped(tmp.pid); // wait for parent to stop, then parent + children should be available

	  // parent sends vector of PIDs for running processes
	  //PID order matches the order of chosen MLBBIDs sent by manager so that ith PID represents ith MLBBID
	  std::vector<uint64_t> pids = receive_vec_dinfo();
	  //Sanity check: first pid returned should be original fork requester	  
	  if (pids[0] != tmp.pid) {
	    LOG_TASE("ERROR: First pid in list should be fork requester's \n");LOG_FLUSH();
	    exit(0);
	  }

	  //Should we do a waitpid on the pids here to make sure they're properly stopped??
	  LOG_TASE("DBG 11 \n"); LOG_FLUSH();
	  std::map<uint64_t, uint64_t> BBIDToPID;
	  for (int i = 0; i < pids.size(); i++) {
	    LOG_TASE("Looping for pid %lu \n", pids[i]);LOG_FLUSH();
	    //I think it's OK to have a BBID of 0. 02112025
	    //if (chosen[i] != 0) {
	    BBIDToPID.insert(std::make_pair(chosen[i], pids[i]));
	      //}
	  }
	  LOG_TASE("Finished making BBIDToPID map with %u entries \n", BBIDToPID.size());LOG_FLUSH();
	  //Remove original fork requester from running, and add it (plus all candidates) to the stopped queue
	  Running->get(&tmp, signals[i].ssi_pid);
	  for (int i = 0; i < candidates.size(); i++){
	    LOG_TASE("Looping dbg1 for time %d \n", i);LOG_FLUSH();
	    auto it = BBIDToPID.find(dests[i]);
	    if (it != BBIDToPID.end()) {
	      candidates[i].pid = it->second;
	      if (candidates[i].pid != tmp.pid) { //We've already waited on the parent
		LOG_TASE("Waiting on pid %d \n", candidates[i].pid);LOG_FLUSH();
		wait_stopped(candidates[i].pid);
	      }
	    } else {
	      candidates[i].pid = -1;  //Will have to replay if scheduled
	    }
	    
	    Stopped->push(candidates[i]);
	  }
	  LOG_TASE("Manager finished handling fork \n"); LOG_FLUSH();
	  
	  /*
	  MOD_TASE("MANAGER in fork_request case \n"); 
	  Running->find(&tmp, signals[i].ssi_pid);
	  
	  WorkerInfo w;
	  w.originator = tmp.pid;	  
	  w.pinfo = tmp.pinfo;
	  
	  MOD_TASE("Trying to call wait_stopped on pid %d \n", (int)signals[i].ssi_pid);
	  wait_stopped((pid_t) signals[i].ssi_pid); // make sure parent has time to set pid of child in pinfo

      	  memcpy((void*)&w.pid, w.pinfo, sizeof(pid_t));  // get child pid
	  
	  MOD_TASE("Forking worker info: pid %d, PID in pinfo: %d\n", w.originator, w.pid);
	
	  // assigning Parent PID here, last of the fork loop
	  if( w.pid == (pid_t) signals[i].ssi_pid ) {
	    //Special case.  We'll assume the last branch sent over is assigned to the parent.
	    //So that implies we need to remove it from the running list. Also, free up its spot in the cache.

	    //Compute a priority if it makes sense for our exploration type.  No priority for BFS or DFS.
	    if ( klee::explorationType == TASEExplorationType::ED || klee::explorationType == TASEExplorationType::ML)
	      predict(&w);
	    
	    MOD_TASE("Synchronizing parent process pid %d\n", tmp.pid);

	    sigval x;
	    x.sival_ptr = w.pinfo; // so we keep the current pinfo value after SIGCONT (see the signal handler above)
	    sigqueue(w.pid, SIGCONT, x); // allow parent to read back updated info
	    
	    //	    MOD_TASE("Waiting on parent process start\n", tmp.pid);
	    //	    wait_started(w.pid);
	    
	    MOD_TASE("Waiting on parent process pid %d\n", tmp.pid);
	    wait_stopped(w.pid);

	    MOD_TASE("Parent process added to Stopped workers\n");
	    //Remove parent from Running, add to Stopped
     	    dealloc_in_cache(w.pinfo);	    
	    Running->get(&tmp, tmp.pid); // using tmp here so we don't wipe new values in w
	    Stopped->push(w);
	    LOG_TASE("Pushing worker %d with priority %lf \n", w.pid, w.priority);LOG_FLUSH(); 
	  } else {
	  //We expect parent to fork off more children for this particular symbolic branch.

	    MOD_TASE("Waiting on child process pid %d\n", w.pid);
	    wait_stopped(w.pid); // make sure child has time to update pinfo

	    //Compute a priority if it makes sense for our exploration type.  No priority for BFS or DFS.
	    if ( klee::explorationType == TASEExplorationType::ED || klee::explorationType == TASEExplorationType::ML)
	      predict(&w);
	    
	    sigval x;
	    x.sival_ptr = w.pinfo; // so we keep the current pinfo value after SIGCONT (see the signal handler above)
	    
	    MOD_TASE("Synchronizing child process pid %d\n", w.pid);
	    sigqueue(w.pid, SIGCONT, x); // allow child to read back updated info
	    
	    //	    MOD_TASE("Waiting on child process start\n", tmp.pid);
	    //	    wait_started(w.pid);
	    
	    MOD_TASE("Waiting on parent child pid %d\n", w.pid);
	    wait_stopped(w.pid);
	    Stopped->push(w);
	    LOG_TASE("Pushing worker %d with priority %lf \n", w.pid, w.priority);LOG_FLUSH();
	    
	    LOG_TASE("child process %d added to Stopped workers\n", w.pid);
	    sigqueue(tmp.pid, SIGCONT, x); // signal parent to continue, possibly forking again
	  }
	  */
	  if( Stopped->size() >= MAX_STOPPED_WORKERS || pickedWorkers >= MAX_PICKED_WORKERS) {
	    if (Stopped->size() >= MAX_STOPPED_WORKERS){
	      LOG_TASE("MAX_STOPPED_WORKERS Exceeded. Execution failed\n");LOG_FLUSH();
	    }
	    if (pickedWorkers >= MAX_PICKED_WORKERS) {
	      LOG_TASE("MAX_PICKED_WORKERS Exceeded. Execution failed\n");LOG_FLUSH();
	    }
	    
	    if (klee::printRecordsOnVerFail == true) {

	      //Populates stats for this weird failure case so we at least have some records.  De-duplicate me later.
	      double costTime = klee::util::getWallTime() - postInitStartTime;
	      costTimes.push_back(costTime);
	      postInitStartTime = klee::util::getWallTime();

	      double arrTime = getCurrMsgArrTime();
	      if (msgCtr == 0) {
		firstMessageArrivalTime = arrTime; //Normalize message arrival times so that first msg comes at time 0
	      }
	      arrTime = arrTime - firstMessageArrivalTime;

	      roundMessageTypes.push_back(getCurrMsgType());
	      roundMessageLengths.push_back(getCurrMsgLen());

	      arrTimes.push_back(arrTime);
	      double compTime;
	      if (msgCtr == 0) {
		compTime = costTime;
	      } else {
		compTime = std::max(arrTimes[msgCtr], compTimes[msgCtr-1]) + costTimes[msgCtr];
	      }
	      compTimes.push_back(compTime);
	      lagTimes.push_back(compTimes[msgCtr] - arrTimes[msgCtr]);
	      roundBranches.push_back(pickedWorkers);
	      infTimes.push_back(inference_time);
	      infCacheHits.push_back(inf_cache_hits);
	      infCacheMisses.push_back(inf_cache_misses);
	      roundReplays.push_back(round_replays);
	      roundReplayTimes.push_back(replay_time);
	      
	      
	      //Todo: De-duplicate this with the other printing we do for LOG_RECORDs
	      if (klee::clientName == "MAVLINK" ) {
		LOG_TASE("LOG_RECORD_FIELDS: ,RUN,MSGIDX,ARR,COST,LAG,BRANCHES,REPLAYS,REPLAYTIME,INFTIME,INFCACHEHITS,INFCACHEMISSES,MSGTYPE,MSGLEN,ELISION_THRESHOLD,ID_STR\n");
		for (int i = 0; i < lagTimes.size(); i++) {
		  LOG_TASE("LOG_RECORD: ,%d,%d,%lf,%lf,%lf,%d,%d,%lf,%lf,%d,%d,%s,%d,%lf,%s\n", (int) klee::mavlinkTraceNum, i,arrTimes[i],costTimes[i], lagTimes[i],roundBranches[i],roundReplays[i],roundReplayTimes[i],infTimes[i],infCacheHits[i], infCacheMisses[i], roundMessageTypes[i].c_str(), roundMessageLengths[i], (double)klee::forkElisionPriorityThreshold, (std::string) klee::logIDStringArg);LOG_FLUSH();
		}
	      } else if (klee::clientName == "TETRINET") {
		for (int i = 0; i < lagTimes.size(); i++) {
		  LOG_TASE("LOG_RECORD: ,%d,%d,%lf,%lf,%lf,%d,%d,%lf,%lf,%d,%d,%lf,%s\n", (int) klee::tetrinetRandomSeed, i,arrTimes[i],costTimes[i], lagTimes[i],roundBranches[i],roundReplays[i],roundReplayTimes[i],infTimes[i],infCacheHits[i],infCacheMisses[i],(double)klee::forkElisionPriorityThreshold,((std::string) klee::logIDStringArg).c_str());LOG_FLUSH();
		}
	      }


	      
	    }
	    cleanUp();
	    exit(1);
	  }
	
	  break;
	}
      }
    }
  }
  clear_signals();
}

void manage_workers() {
  // while( (!success || !Stopped->empty() || !Running->empty() )) {
  while( !success && !(Stopped->empty() && Running->empty()) ) {
    MOD_TASE("Manager calling schedule_worker with %ld workers in Stopped \n",Stopped->size());
    while( !Stopped->empty() && schedule_worker() ){}
    MOD_TASE("%ld workers in Stopped before handle_signals \n", Stopped->size());
    handle_signals();
    MOD_TASE("%ld workers in Stopped after handle_signals \n", Stopped->size()); 
  }

  LOG_TASE("All workers finished.\n"); 
  delete Stopped;
  delete Running;
}

void worker_success (WorkerGroup * Stopped, WorkerGroup * Running) {
  fflush(prev_stdout_log);
  LOG_FLUSH();
  
  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::SUCCESS);
  sigqueue(manager_pid, SIGSTD, x);

  workerPrepForReplay();
  
}

void worker_error(WorkerGroup *Stopped, WorkerGroup *Running) {
  fflush(prev_stdout_log);
  LOG_FLUSH();
  
  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::ERROR);
  sigqueue(manager_pid, SIGSTD, x);
}

//------------------------------------------------

int semID; //Global semaphore ID for sync

struct sembuf sem_lock = {0, -1, 0 | SEM_UNDO}; // {sem index, inc/dec, flags}
struct sembuf sem_unlock = {0, 1, 0 | SEM_UNDO};// SEM_UNDO added to release
//lock if process dies.

void get_sem_lock () {
  int res =  semop(semID, &sem_lock, 1);
  if (res == 0) {
    return;
  } else {
    printf("Error getting sem lock \n");
    std::cout.flush();
    perror("Error in get_sem_lock");
    std::exit(EXIT_FAILURE);
  }
}

void release_sem_lock () {
  int res = semop(semID, &sem_unlock, 1);
  if (res == 0) {
    return;
  } else {
    perror("Error in release_sem_lock");
    std::exit(EXIT_FAILURE);
  }
}

int initialize_semaphore(int semKey) {
  semID = semget(semKey, 1, IPC_CREAT |IPC_EXCL | 0660 );
  if ( semID == -1) {
    perror("Error creating semaphore ");
    std::exit(EXIT_FAILURE);
  }
  //Todo -- Double check to see if we need to initialize
  //semaphore explicitly to 1.
  int res = semctl(semID, 0, SETVAL, 1);
  if (res == -1) {
    perror("Error initializing semaphore \n");
    std::exit(EXIT_FAILURE);
  }
  return semID;
}

int * MLIDPtr; //Ptr to an int representing largest ID allocated so far
void initSharedMLIDMem() {
  DBG_TASE("Calling initSharedMLIDMem \n");
  initialize_semaphore(getpid());
  void * MLIDBuf = mmap(NULL, 100, PROT_READ|PROT_WRITE, MAP_ANON|MAP_SHARED, -1, 0);
  MLIDPtr = (int *) MLIDBuf;
  *MLIDPtr = 0;
}

int getNewMLID() {
  get_sem_lock();
  *MLIDPtr = *MLIDPtr + 1;
  int val = *MLIDPtr;


  release_sem_lock();
  return val;
}

//Get index of val in vector vals or DIE TRYIN
int getIdxInVec(std::vector<uint64_t> vals, uint64_t val) {
  for (int i = 0; i < vals.size(); i++) {
    if (vals[i] == val)
      return i;
  }
  LOG_TASE("ERROR: Could not find val %lu in vector of vals \n", val);LOG_FLUSH();
  exit(0);//This should be a hard error, full stop on verification
  return -1;
}

int tase_fork_inner(std::vector<uint64_t> dests, std::vector<std::vector<float>>cbows) {

  //Ignore this case if we're not doing fork elision.
  LOG_TASE("DBG 88 \n");LOG_FLUSH();
  if (klee::useFallBackOracle && inForkElisionReplay) {
    std::vector<uint64_t> tmp = getExecutionFragment();
    if (tmp.size() == 0) {
      LOG_TASE("Looks like we have a failback replay \n");LOG_FLUSH();
      inForkElisionReplay = false;
    }
  }
  
  if(inForkElisionReplay) {
    std::vector<uint64_t> frag = getExecutionFragment();
    LOG_TASE("Frag is len %d, replayctr is %d, dests is %d \n", frag.size(), forkElisionReplayCtr, dests.size());LOG_FLUSH();
    
    for (int i = 0; i < dests.size(); i++) {
      LOG_TASE("DBG 99 \n");LOG_FLUSH();
      if (dests[i] == frag[forkElisionReplayCtr]) {
	LOG_TASE("DBG 100 \n");LOG_FLUSH();
	forkElisionReplayCtr++;
	LOG_TASE("PID %d replaying through MLBBID %lu \n", frag[forkElisionReplayCtr]);LOG_FLUSH();
	if (forkElisionReplayCtr == frag.size()) {
	  inForkElisionReplay = false;
	  forkElisionReplayCtr = -1;
	  LOG_TASE("PID %d done replaying frag of size %d \n", frag.size());
	}
	
	return i;
      }
    }
    
    LOG_TASE("FATAL ERROR in fork elision replay: could not find MLBBID %lu in %d dests \n", frag[forkElisionReplayCtr], frag.size());
    LOG_FLUSH();
    exit(0);
  }    
  

  // fill destinations, Signal manager (FORK_REQUEST, PID ) then SIGSTOP.
  // when continued (SIGCONT), check destinations returned.
  // only fork if manager returned more than one destination, otherwise just return that destination (possible fork \
elision).
  double T0 = klee::util::getWallTime();
  LOG_TASE("Worker %d entering tase_fork_inner \n", getpid());LOG_FLUSH();
  copy_worker_info();// local -> shared, feats before applying each dest
  LOG_TASE("DBG time 0 %lf \n", klee::util::getWallTime() - T0); LOG_FLUSH();
  LOG_TASE("Copied worker info \n");LOG_FLUSH();

  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
  sigqueue(manager_pid, SIGSTD, x);
  kill(getpid(), SIGSTOP);
  LOG_TASE("Sent vec dinfo \n"); LOG_FLUSH();
  send_vec_dinfo(&dests);
  if (klee::useLEARCHFeatsOracle) {
    send_cbow_feats(&cbows);
  }
  LOG_TASE("DBG time 1 %lf \n", klee::util::getWallTime() - T0); LOG_FLUSH();
  kill(getpid(), SIGSTOP);
  LOG_TASE("DBG time 1.5 %lf \n", klee::util::getWallTime() - T0); LOG_FLUSH();
  LOG_TASE("Calling receive_vec_dinfo \n");LOG_FLUSH();
  std::vector<uint64_t> BBIDsToFork = receive_vec_dinfo();
  std::vector<uint64_t> forkedPIDs;
  LOG_TASE("DBG time 2 %lf \n", klee::util::getWallTime() - T0); LOG_FLUSH();
  forkedPIDs.push_back((uint64_t) getpid()); //Slot 0 for parent pid
  LOG_TASE("DBG1 \n");LOG_FLUSH();
  for( unsigned int i = 1; i < BBIDsToFork.size(); i++ ) {  // save one for current process
    int pid = call_fork();
    if( pid == 0 ) { // child
      cycleTASELogs(false);
      renew_fds();
      kill(getpid(), SIGSTOP);
      retrieve_worker_info();
      return getIdxInVec(dests,BBIDsToFork[i]);  //Bad for large dests vec
    } else { // parent
      LOG_TASE("Parent returned from forking pid %d \n", pid);LOG_FLUSH();
      forkedPIDs.push_back((uint64_t) pid);
    }
  }
  LOG_TASE("Spend %lf seconds on core tase_fork_inner \n", klee::util::getWallTime() - T0);LOG_FLUSH();
  
  send_vec_dinfo(&forkedPIDs);
  LOG_TASE("DBG2 \n");LOG_FLUSH();
  
  kill(getpid(), SIGSTOP);
  LOG_TASE("DBG3 \n");LOG_FLUSH();
  retrieve_worker_info(); //When we're hit with a SIGCONT, better have pinfo pointed correctly
  LOG_TASE("DBG4 \n");LOG_FLUSH();
  LOG_TASE("Spend %lf seconds on total tase_fork_inner \n", klee::util::getWallTime() - T0);LOG_FLUSH();
  return getIdxInVec(dests,BBIDsToFork[0]); //Bad for large dests vec
}


int tase_fork_RIP(std::vector<uint64_t> dests, std::vector<std::vector<float>> RIP_Constraint_BOWs) {
  MOD_TASE("PID %d Calling regular tase_fork_RIP with %ld destinations\n", getpid(), dests.size()); LOG_FLUSH();

  std::vector<uint64_t> bbids;
  for( auto x : dests ) {
    bbids.push_back(getMLBBID(x));
  }
  int res = tase_fork_inner(bbids, RIP_Constraint_BOWs);
  if (res >= dests.size() || res < 0) {
    LOG_TASE("Bad index %d returned in tase_fork_RIP \n", res);LOG_FLUSH();
    exit(0);
  }
  return res;
  
}
  


int tase_fork_RIP_old(std::vector<uint64_t> dests) {
  MOD_TASE("PID %d Calling regular tase_fork_RIP from orig RIP 0x%lx \n", getpid(), pre_interp_RIP);
  LOG_TASE("AHDBG PID %d produced dests from orig RIP 0x%lx during tase_fork_RIP ", getpid(), pre_interp_RIP);
  for (int i = 0; i < dests.size(); i++) {
    LOG_TASE("0x%lx ", dests[i]);
  }
  LOG_TASE("\n");
  //  std::vector<uint64_t> MLBBIDs;
  //  for (int i = 0; i < dests.size(); i++) {
    //    MLBBIDs.push_back(getMLBBID(dests[i]));
    //    DBG_TASE("MLBBID is %ld and 0x%lx in hex \n", getMLBBID(dests[i]),  getMLBBID(dests[i])); 
    //  }
  //  checkMLBBIDs(MLBBIDs);
    
  for (int i = 0; i < dests.size()-1; i++) {
    int pid = call_fork();
    
    if (pid == 0) {// Child
      cycleTASELogs(false);
      renew_fds();
      
      LOG_TASE("updating worker info with dest %lx\n", dests[i]);LOG_FLUSH();
      update_worker_info(getMLBBID(dests[i])); // update local copy + pid
      copy_worker_info(); // move local copy into shared mem
    
      kill(getpid(), SIGSTOP); // let manager predict
      retrieve_worker_info();
      kill(getpid(), SIGSTOP); // added to Stopped queue
      LOG_TASE("AHDBG PID %d exiting from tase_forkPQ as child with dest RIP 0x%lx \n", getpid(), dests[i]);LOG_FLUSH();
      return i; // breaks child out of loop, no forkbomb
    } else {// Parent

      MOD_TASE("Parent %d produced child %d \n", getpid(), pid);

      *reinterpret_cast<pid_t*>(workerInfo.pinfo) = pid;
      
      //Signal to manager here:
      sigval x;
      x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
      sigqueue(manager_pid, SIGSTD, x);
      
      kill(getpid(), SIGSTOP); //Wait for manager to SIGCONT us to confirm child data has been read
    }
  }

  *reinterpret_cast<pid_t*>(workerInfo.pinfo) = getpid();
  
  DBG_TASE("Parent special case \n");

  update_worker_info(getMLBBID(dests[dests.size()-1])); // updates local info
  copy_worker_info(); // move local struct into shared mem

  //Signal to manager here:
  sigval x;
  DBG_TASE("Parent signaling \n"); 
  x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
  sigqueue(manager_pid, SIGSTD, x);

  DBG_TASE("Parent sigstopping self \n"); 
  kill(getpid(), SIGSTOP);
  retrieve_worker_info();
  kill(getpid(), SIGSTOP);
  
  DBG_TASE("PID %d exiting from tase_forkPQ \n", getpid()); 
  LOG_TASE("AHDBG PID %d exiting from tase_forkPQ as parent with dest RIP 0x%lx \n", getpid(), dests[dests.size() -1]);LOG_FLUSH();
  return dests.size()-1;
}

//Return 1 for trueBranchID, 0 for false
int tase_fork_IR(uint64_t trueBranchID, uint64_t falseBranchID, std::vector<std::vector<float>> IR_Constraint_BOWs) {
  //Swap true/false in dests so that tase_fork_inner returning 0 is for false branch, 1 for true
  //We should probably refactor so that the args take the branchIDs in reversed order.
  std::vector<uint64_t> dests;
  dests.push_back(falseBranchID);
  dests.push_back(trueBranchID);
  LOG_TASE("DBG 77 \n");LOG_FLUSH();
  int res = tase_fork_inner(dests, IR_Constraint_BOWs);
  if (res != 0 && res != 1) {
    LOG_TASE("tase_fork_IR should return 0 or 1, not %d \n", res);LOG_FLUSH();
    exit(0);
  }
  return res;
}

int tase_fork_IR_old(uint64_t trueBranchID, uint64_t falseBranchID) {
  MOD_TASE("AHDBG PID %d calling tase_forkIR_PQ with branch IDs %ld and %ld from orig rip 0x%lx \n", getpid(), trueBranchID, falseBranchID, pre_interp_RIP); 
  MOD_TASE("branches in hex: 0x%lx and 0x%lx \n", trueBranchID, falseBranchID); 
  
  int pid = call_fork();
  
  //False branch for child
  if (pid == 0) {
    cycleTASELogs(false);
    renew_fds();
    workerInfo.pid = getpid();
    update_worker_info(falseBranchID); // update local copy
    copy_worker_info(); // move local struct into shared mem

    kill(workerInfo.pid, SIGSTOP);
    retrieve_worker_info();
    kill(workerInfo.pid, SIGSTOP);
    
    MOD_TASE("Child %d advancing from tase_forkIR_PQ \n", getpid()); 
    return 0;

  } else {
    //Signal to manager
    *reinterpret_cast<pid_t*>(workerInfo.pinfo) = pid;
    
    sigval x;
    x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
    sigqueue(manager_pid, SIGSTD, x);
    //Wait for manager to SIGCONT us to confirm child data has been read
    kill(getpid(), SIGSTOP);

    //Assign (arbitrarily) true branch to parent
    MOD_TASE("Parent special case \n");
    
    *reinterpret_cast<pid_t*>(workerInfo.pinfo) = getpid();
    update_worker_info(trueBranchID); // update local copy
    copy_worker_info(); // move local struct into shared mem
    
    //Signal to manager here:
    MOD_TASE("Parent signaling \n"); 
    x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
    sigqueue(manager_pid, SIGSTD, x);

    MOD_TASE("Parent sigstopping self \n"); 
    kill(getpid(), SIGSTOP);
    retrieve_worker_info();
    kill(getpid(), SIGSTOP);
    
    MOD_TASE("Parent returned from sigstop \n");
    return 1;
  }
}

//Stuff a bunch of random priority items into our max priority queue,
//and make sure we extract the items from highest to lowest priority.
void testPQ(int PQTestSize) {
  srand(time(NULL));  
  WorkerGroup * testGroup = new WorkerGroup(PQ);  

  //Make random priorities and stick them in the PQ
  std::vector<double> priorities;
  for (int i = 0; i < PQTestSize; i++) {
    double randNum = (double) rand() /((double) RAND_MAX);
    WorkerInfo w;
    w.priority = randNum;
    priorities.push_back(randNum);
    testGroup->push(w);
  }  
  std::sort(priorities.begin(), priorities.end());  //Sorts low to high

  //Grab all the workers from the PQ in order from highest to lowest priority
  std::vector<double> prioritiesFromPQ;
  for (int i = 0; i < PQTestSize; i++) {
    WorkerInfo w = testGroup->pop();
    prioritiesFromPQ.push_back(w.priority);
  }
  //Reverse because PQ items are (or should be) emitted high to low
  std::reverse(prioritiesFromPQ.begin(), prioritiesFromPQ.end()); 

  //If PQ is working, the orders of the priorities from PQ should match our sorted list 
  if (priorities.size() != prioritiesFromPQ.size()) {    
    LOG_TASE("testPQ Failed: size mismatch in vectors \n");LOG_FLUSH();
    exit(0);
  } else {
    if (priorities != prioritiesFromPQ) { //spooky vector comparison
      LOG_TASE("testPQ Failed: vector contents wrong \n"); LOG_FLUSH();
      exit(0);
    } else {
      LOG_TASE("testPQ Passed: vector priorities retrieved in correct order \n");LOG_FLUSH();
      for (int i = 0; i < PQTestSize; i++) {
	LOG_TASE("%lf \n", priorities[i]);LOG_FLUSH();
      }
      exit(0);
    }
  }
}

//This is a graphical representation of nodes and children.
//Children appear below their parent, connected with a line.
//We use this to test BFS and DFS.  Relationships between
//a node and child are given by testGetChildIDs below.

/*
     (  1  )
    /   |   \
   (2) (3)  (4 )
   |    |    |  \
  (5)  (6)  (7) (8)
       / \    \
     (9) (10) (11)
               |
              (12)
*/


//Given an id, produce the children of that id
//(e.g., 1 -> (2,3,4).
//This is a helper fn for testing the order in which nodes are explored
//for BFS and DFS in testBFS() and testDFS()
std::vector<int>testGetChildIDs (int i ) {
  if (i == 1) {
    return std::vector<int> {2,3,4};
  } else if (i == 2) {
    return std::vector<int> {5};
  } else if (i == 3) {
    return std::vector<int> {6};
  } else if (i == 4) {
    return std::vector<int> {7,8};
  } else if (i == 5) {
    return std::vector<int> {};
  } else if (i == 6) {
    return std::vector<int> {9,10};
  } else if (i == 7) {
    return std::vector<int> {11};
  } else if (i == 8) {
    return std::vector<int> {};
  } else if (i == 9) {
    return std::vector<int> {};
  } else if (i == 10) {
    return std::vector<int> {};
  } else if (i == 11) {
    return std::vector<int>{12};
  } else if (i == 12) {
    return std::vector<int> {};
  } else {
    LOG_TASE("ERROR in testGetChildIDs \n");LOG_FLUSH();
    exit(0);
    return std::vector<int>{};
  }
}

//Test BFS.  You will have to manually examine the
//order in which nodes are visited in the log to determine if the
//nodes are visited in accordance with BFS.
void testBFS() {
  LOG_TASE("Running test for BFS \n");LOG_FLUSH();
  WorkerGroup * testGroup = new WorkerGroup(QUEUE);
  WorkerInfo w1;
  w1.pid = 1;
  testGroup->push(w1);
  while (!testGroup->empty()) {
    WorkerInfo curr = testGroup->pop();
    int nodeID = curr.pid;
    LOG_TASE("Visiting node %d in test BFS \n", nodeID);LOG_FLUSH();
    std::vector<int> childrenIDs = testGetChildIDs(nodeID);
    for (int i = 0; i < childrenIDs.size(); i++) {
      WorkerInfo kidInfo;
      kidInfo.pid = childrenIDs[i];
      testGroup->push(kidInfo);
    } 
  }
}


//Test DFS.  You will have to manually examine the
//order in which nodes are visited in the log to determine if the
//nodes are visited in accordance with DFS.
void testDFS() {
  LOG_TASE("Running test for DFS \n");LOG_FLUSH();
  WorkerGroup * testGroup = new WorkerGroup(STACK);
  WorkerInfo w1;
  w1.pid = 1;
  testGroup->push(w1);
  while (!testGroup->empty()) {
    WorkerInfo curr = testGroup->pop();
    int nodeID = curr.pid;
    LOG_TASE("Visiting node %d in test DFS \n", nodeID);LOG_FLUSH();
    std::vector<int> childrenIDs = testGetChildIDs(nodeID);
    for (int i = 0; i < childrenIDs.size(); i++) {
      WorkerInfo kidInfo;
      kidInfo.pid = childrenIDs[i];
      testGroup->push(kidInfo);
    }
  }
}


//For performance debugging:
int getNumOpenFDs() {

  DIR * dir;
  dir = opendir("/proc/self/fd");
  if (dir == NULL) {
    perror("Couldn't open /proc/self/fd dir \n");
    LOG_TASE("Couldn't open /proc/self/fd dir \n"); LOG_FLUSH();
    exit(0);
  }
  
  int numFDs = 0;
  struct dirent * entryPtr;
  while ((entryPtr = readdir(dir)) !=  NULL) {
    if (entryPtr->d_type == DT_LNK) {
      numFDs++;
    }
  }

  closedir(dir);
  return numFDs;
  
}
