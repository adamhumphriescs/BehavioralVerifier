


//===-- Executor.cpp ------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "Executor.h"
#include "Context.h"
#include "CoreStats.h"
#include "ExternalDispatcher.h"
#include "ImpliedValue.h"
#include "Memory.h"
#include "MemoryManager.h"
#include "PTree.h"
#include "Searcher.h"
#include "SeedInfo.h"
#include "SpecialFunctionHandler.h"
#include "StatsTracker.h"
#include "TimingSolver.h"
#include "UserSearcher.h"
#include "ExecutorTimerInfo.h"


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

#include <immintrin.h>

extern double postInitStartTime;
using namespace llvm;
using namespace klee;

//AH: Our additions below. --------------------------------------

#include <iostream>
#include "klee/CVAssignment.h"
#include "klee/util/ExprUtil.h"
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <netdb.h>
#include <fcntl.h>
#include "API.h"
#include "tase_shims.h"
//#include "tase/TASEControl.h"
#include "../Tase/TASESoftFloatEmulation.h"
#include <sys/times.h>
#include <sys/time.h>
#include <sys/sendfile.h>
#include <unordered_set>
//Can't include signal.h directly if it has conflicts with our tase_interp.h definitions
//on enums like GREG_RSI, GREG_RDI, etc.
extern "C"  void ( *signal(int signum, void (*handler)(int)) ) (int){
  return NULL;
  }

extern "C" void sb_modeled();
extern uint64_t tase_openedTran_ctr;
extern uint64_t tase_closedTran_ctr;
extern uint64_t tase_xbegin_ctr;
extern uint64_t tase_xend_ctr;
extern uint64_t tase_xrestart_ctr;
extern uint64_t tase_mem;
extern uint64_t tase_reg;
extern uint64_t cartridge_rip;
extern uint64_t rsp_global;

extern bool inPriorityTest;

//Symbols we need to map in for TASE
//extern bool taseDebug;
//extern bool modelDebug;
extern int localStack;
extern bool noLog;

double coreInterpStartTime = 0;

extern char edata;
extern char __GNU_EH_FRAME_HDR,  _IO_stdin_used; //used for mapping .rodata section
extern int __ctype_tolower;
extern char ** environ;
extern int * __errno_location();
extern "C" int __isoc99_sscanf ( const char * s, const char * format, ...);

extern std::string logFile;

//TASE internals--------------------
extern uint16_t poison_val;
extern target_ctx_t target_ctx;
extern tase_greg_t * target_ctx_gregs;

extern int retryMax;
extern Module * interpModule;
extern klee::Interpreter * GlobalInterpreter;
extern std::unordered_set<uint64_t> cartridge_entry_points;
extern std::unordered_set<uint64_t> cartridges_with_flags_live;
extern std::unordered_map<uint64_t, std::pair<int32_t, int32_t>> cartridge_regstatus;

extern double target_start_time;
extern double target_end_time;

extern std::unordered_set<uint32_t> kill_flags;

UFManager *ufmanager;
UFManager *ufmanager_cheat;

Executor * GlobalExecutorPtr;
MemoryObject * target_ctx_gregs_MO;
ObjectState * target_ctx_gregs_OS;
//MemoryObject * target_ctx_xmms_MO;
//ObjectState * target_ctx_xmms_OS;
ExecutionState * GlobalExecutionStatePtr;
void * rodata_base_ptr;
uint64_t rodata_size;
uint64_t bounceback_offset = 0;
extern uint64_t trap_off;//+8 + 6 + 7;  //Offset from function address at which we trap adding +7 for mov isntruction  Taint_sara
std::map<uint64_t, KFunction *> IR_KF_Map;
std::vector<ref<Expr> > arguments;

extern "C" void make_byte_symbolic(void * addr);

//TASE stats and logging

extern uint64_t tranMaxArg;
uint64_t interpCtr =0;
uint64_t instCtr = 0;
int forkSolverCalls = 0;
std::string prev_unique_log_ID = "NONE";
std::string curr_unique_log_ID = "ROOT";
extern std::stringstream worker_ID_stream;
extern std::string prev_worker_ID;

FILE * prev_stdout_log = NULL;
//FILE * prev_stderr_log = NULL;

//extern "C" void cycleTASELogs(bool isReplay);
//bool isSpecialInst(uint64_t rip);
extern "C" bool tase_buf_has_taint (const void * ptr, const int size);
//void printCtx(tase_greg_t *);

//Multipass
extern int c_special_cmds; //Int used by cliver to disable special commands to s_client.  Made global for debugging
extern bool UseForkedCoreSolver;
		 //extern bool singleStepping;
extern int round_count;
extern int pass_count;
extern int run_count;
int multipass_symbolic_vars = 0;
extern CVAssignment prevMPA;
std::vector<const klee::Array *> round_symbolics;

extern bool tetriTest;

//Addition from cliver
std::map<std::string, uint64_t> array_name_index_map_;
std::string get_unique_array_name(const std::string &s) {
  // Look up unique name for this variable, incremented per variable name
  return s + "_" + llvm::utostr(array_name_index_map_[s]++);
}


//Todo: Move this out!
//Mavlink encoding:
/*
std::map<double, std::vector<float>> CurrBBEncodingMap = {
							  {10, std::vector<float> {1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {12, std::vector<float> {0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {15, std::vector<float> {0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {16, std::vector<float> {0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {17, std::vector<float> {0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {20, std::vector<float> {0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {23, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {26, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {29, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {32, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {35, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {38, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {41, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {44, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {47, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {50, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {53, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {56, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {59, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {62, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {65, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {68, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {71, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {74, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {77, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {80, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {83, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {86, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {89, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {92, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {95, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {98, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0}},
							  {101, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0}},
							  {822, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0}},
							  {823, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0}},
							  {863, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0}},
							  {864, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0}}
};
*/
//Tetrinet

std::map<double, std::vector<float>> CurrBBEncodingMap = {
							  {626, std::vector<float> {1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {639, std::vector<float> {0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {641, std::vector<float> {0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {645, std::vector<float> {0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {647, std::vector<float> {0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {657, std::vector<float> {0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {691, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {692, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {694, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {728, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {759, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {801, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {810, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1995, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1996, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1997, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {2008, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {2011, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {2025, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {14355223812245442, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {15199648742376068, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0}},
							  {15199648742377411, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0}},
							  {15762598695797380, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0}},
							  {15762598695798722, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0}},
							  {15762598695798723, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0}},
							  {16044073672509378, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0}}
};

/*
std::map<double, std::vector<float>> CurrBBEncodingMap = {
							  {717, std::vector<float> {1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {718, std::vector<float> {0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {719, std::vector<float> {0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {730, std::vector<float> {0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {733, std::vector<float> {0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {747, std::vector<float> {0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1453, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1466, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1468, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1472, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1474, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1484, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1518, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1519, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1521, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1555, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1586, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1628, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {1637, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {14355223812244164, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0,0.0}},
							  {15199648742376133, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0,0.0}},
							  {15199648742376895, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0,0.0}},
							  {15762598695797444, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0,0.0}},
							  {15762598695797445, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0,0.0}},
							  {15762598695798207, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0,0.0}},
							  {16044073672508100, std::vector<float> {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0,1.0}}
};
*/
//Todo : fix these functions and remove traps
#ifdef TASE_OPENSSL

extern "C" {
  void RAND_add(const void * buf, int num, double entropy);
  int RAND_load_file(const char *filename, long max_bytes);
}

	
void OpenSSLDie (const char * file, int line, const char * assertion);

extern "C" {
  int RAND_poll();
  int tls1_generate_master_secret(SSL *s, unsigned char *out, unsigned char *p, int len);
  int ssl3_connect(SSL *s);
  void gcm_gmult_4bit(u64 Xi[2],const u128 Htable[16]);
  void gcm_ghash_4bit(u64 Xi[2],const u128 Htable[16],const u8 *inp,size_t len);
}

extern void multipass_reset_round(bool isFirstCall);
extern void multipass_start_round (klee::Executor * theExecutor, bool isReplay);

//Distinction between prohib_fns and modeled_fns is that we sometimes may want to "jump back" into native execution
//for prohib_fns.  Modeled fns are always skipped and emulated with a return.
static const uint64_t prohib_fns [] = { (uint64_t) &AES_encrypt, (uint64_t) &ECDH_compute_key, (uint64_t) &EC_POINT_point2oct, (uint64_t) &EC_KEY_generate_key, (uint64_t) &SHA1_Update, (uint64_t) &SHA1_Final, (uint64_t) &SHA256_Update, (uint64_t) &SHA256_Final, (uint64_t) &gcm_gmult_4bit, (uint64_t) &gcm_ghash_4bit, (uint64_t) &tls1_generate_master_secret };
#endif // TASE_OPENSSL


// Network capture for Cliver
extern "C" { int ktest_connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen);
  int ktest_select(int nfds, fd_set *readfds, fd_set *writefds,
		   fd_set *exceptfds, struct timeval *timeout);
  ssize_t ktest_writesocket(int fd, const void *buf, size_t count);
  ssize_t ktest_readsocket(int fd, void *buf, size_t count);
  // stdin capture for Cliver
  int ktest_raw_read_stdin(void *buf, int siz);
  // Random number generator capture for Cliver
  int ktest_RAND_bytes(unsigned char *buf, int num);
  int ktest_RAND_pseudo_bytes(unsigned char *buf, int num);
  // Time capture for Cliver (actually unnecessary!)
  time_t ktest_time(time_t *t);
  // TLS Master Secret capture for Cliver
  void ktest_master_secret(unsigned char *ms, int len);
  void ktest_start(const char *filename, enum kTestMode mode);
  void ktest_finish();               // write capture to file  
}


namespace {
  cl::opt<bool>
  DumpStatesOnHalt("dump-states-on-halt",
                   cl::init(true),
		   cl::desc("Dump test cases for all active states on exit (default=on)"));
  
  cl::opt<bool>
  AllowExternalSymCalls("allow-external-sym-calls",
                        cl::init(false),
			cl::desc("Allow calls with symbolic arguments to external functions.  This concretizes the symbolic arguments.  (default=off)"));

  /// The different query logging solvers that can switched on/off
  enum PrintDebugInstructionsType {
    STDERR_ALL, ///
    STDERR_SRC,
    STDERR_COMPACT,
    FILE_ALL,    ///
    FILE_SRC,    ///
    FILE_COMPACT ///
  };

  llvm::cl::bits<PrintDebugInstructionsType> DebugPrintInstructions(
      "debug-print-instructions",
      llvm::cl::desc("Log instructions during execution."),
      llvm::cl::values(
          clEnumValN(STDERR_ALL, "all:stderr", "Log all instructions to stderr "
                                               "in format [src, inst_id, "
                                               "llvm_inst]"),
          clEnumValN(STDERR_SRC, "src:stderr",
                     "Log all instructions to stderr in format [src, inst_id]"),
          clEnumValN(STDERR_COMPACT, "compact:stderr",
                     "Log all instructions to stderr in format [inst_id]"),
          clEnumValN(FILE_ALL, "all:file", "Log all instructions to file "
                                           "instructions.txt in format [src, "
                                           "inst_id, llvm_inst]"),
          clEnumValN(FILE_SRC, "src:file", "Log all instructions to file "
                                           "instructions.txt in format [src, "
                                           "inst_id]"),
          clEnumValN(FILE_COMPACT, "compact:file",
                     "Log all instructions to file instructions.txt in format "
                     "[inst_id]")
          KLEE_LLVM_CL_VAL_END),
      llvm::cl::CommaSeparated);
#ifdef HAVE_ZLIB_H
  cl::opt<bool> DebugCompressInstructions(
      "debug-compress-instructions", cl::init(false),
      cl::desc("Compress the logged instructions in gzip format."));
#endif

  cl::opt<bool>
  DebugCheckForImpliedValues("debug-check-for-implied-values");


  cl::opt<bool>
  SimplifySymIndices("simplify-sym-indices",
                     cl::init(false),
		     cl::desc("Simplify symbolic accesses using equalities from other constraints (default=off)"));

  cl::opt<bool>
  EqualitySubstitution("equality-substitution",
		       cl::init(true),
		       cl::desc("Simplify equality expressions before querying the solver (default=on)."));
 
  cl::opt<unsigned>
  MaxSymArraySize("max-sym-array-size",
                  cl::init(0));

  cl::opt<bool>
  SuppressExternalWarnings("suppress-external-warnings",
			   cl::init(false),
			   cl::desc("Supress warnings about calling external functions."));

  cl::opt<bool>
  AllExternalWarnings("all-external-warnings",
		      cl::init(false),
		      cl::desc("Issue an warning everytime an external call is made," 
			       "as opposed to once per function (default=off)"));

  cl::opt<bool>
  OnlyOutputStatesCoveringNew("only-output-states-covering-new",
                              cl::init(false),
			      cl::desc("Only output test cases covering new code (default=off)."));

  cl::opt<bool>
  EmitAllErrors("emit-all-errors",
                cl::init(false),
                cl::desc("Generate tests cases for all errors "
                         "(default=off, i.e. one per (error,instruction) pair)"));
  
  cl::opt<bool>
  NoExternals("no-externals", 
           cl::desc("Do not allow external function calls (default=off)"));

  cl::opt<bool>
  AlwaysOutputSeeds("always-output-seeds",
		    cl::init(true));

  cl::opt<bool>
  OnlyReplaySeeds("only-replay-seeds",
		  cl::init(false),
                  cl::desc("Discard states that do not have a seed (default=off)."));
 
  cl::opt<bool>
  OnlySeed("only-seed",
	   cl::init(false),
           cl::desc("Stop execution after seeding is done without doing regular search (default=off)."));
 
  cl::opt<bool>
  AllowSeedExtension("allow-seed-extension",
		     cl::init(false),
                     cl::desc("Allow extra (unbound) values to become symbolic during seeding (default=false)."));
 
  cl::opt<bool>
  ZeroSeedExtension("zero-seed-extension",
		    cl::init(false),
		    cl::desc("(default=off)"));
 
  cl::opt<bool>
  AllowSeedTruncation("allow-seed-truncation",
		      cl::init(false),
                      cl::desc("Allow smaller buffers than in seeds (default=off)."));
 
  cl::opt<bool>
  NamedSeedMatching("named-seed-matching",
		    cl::init(false),
                    cl::desc("Use names to match symbolic objects to inputs (default=off)."));

  cl::opt<double>
  MaxStaticForkPct("max-static-fork-pct", 
		   cl::init(1.),
		   cl::desc("(default=1.0)"));

  cl::opt<double>
  MaxStaticSolvePct("max-static-solve-pct",
		    cl::init(1.),
		    cl::desc("(default=1.0)"));

  cl::opt<double>
  MaxStaticCPForkPct("max-static-cpfork-pct", 
		     cl::init(1.),
		     cl::desc("(default=1.0)"));

  cl::opt<double>
  MaxStaticCPSolvePct("max-static-cpsolve-pct",
		      cl::init(1.),
		      cl::desc("(default=1.0)"));

  cl::opt<double>
  MaxInstructionTime("max-instruction-time",
                     cl::desc("Only allow a single instruction to take this much time (default=0s (off)). Enables --use-forked-solver"),
                     cl::init(0));
  
  cl::opt<double>
  SeedTime("seed-time",
           cl::desc("Amount of time to dedicate to seeds, before normal search (default=0 (off))"),
           cl::init(0));
  
  cl::list<Executor::TerminateReason>
  ExitOnErrorType("exit-on-error-type",
		  cl::desc("Stop execution after reaching a specified condition.  (default=off)"),
		  cl::values(
		    clEnumValN(Executor::Abort, "Abort", "The program crashed"),
		    clEnumValN(Executor::Assert, "Assert", "An assertion was hit"),
		    clEnumValN(Executor::BadVectorAccess, "BadVectorAccess", "Vector accessed out of bounds"),
		    clEnumValN(Executor::Exec, "Exec", "Trying to execute an unexpected instruction"),
		    clEnumValN(Executor::External, "External", "External objects referenced"),
		    clEnumValN(Executor::Free, "Free", "Freeing invalid memory"),
		    clEnumValN(Executor::Model, "Model", "Memory model limit hit"),
		    clEnumValN(Executor::Overflow, "Overflow", "An overflow occurred"),
		    clEnumValN(Executor::Ptr, "Ptr", "Pointer error"),
		    clEnumValN(Executor::ReadOnly, "ReadOnly", "Write to read-only memory"),
		    clEnumValN(Executor::ReportError, "ReportError", "klee_report_error called"),
		    clEnumValN(Executor::User, "User", "Wrong klee_* functions invocation"),
		    clEnumValN(Executor::Unhandled, "Unhandled", "Unhandled instruction hit")
		    KLEE_LLVM_CL_VAL_END),
		  cl::ZeroOrMore);

  cl::opt<unsigned long long>
  StopAfterNInstructions("stop-after-n-instructions",
                         cl::desc("Stop execution after specified number of instructions (default=0 (off))"),
                         cl::init(0));
  
  cl::opt<unsigned>
  MaxForks("max-forks",
           cl::desc("Only fork this many times (default=-1 (off))"),
           cl::init(~0u));
  
  cl::opt<unsigned>
  MaxDepth("max-depth",
           cl::desc("Only allow this many symbolic branches (default=0 (off))"),
           cl::init(0));
  
  cl::opt<unsigned>
  MaxMemory("max-memory",
            cl::desc("Refuse to fork when above this amount of memory (in MB, default=2000)"),
            cl::init(2000));

  cl::opt<bool>
  MaxMemoryInhibit("max-memory-inhibit",
            cl::desc("Inhibit forking at memory cap (vs. random terminate) (default=on)"),
            cl::init(true));
}



EXECUTION_STATE ex_state;
ABORT_INFO abort_info{};

// only occurs w/ mixed-mode checks. INTERP_ONLY mode makes this always false, see update()
bool EXECUTION_STATE::is_concrete() const {
  return (txn_status & CONCRETE) != 0;
}

// singleStepping makes this always true, see update()
bool EXECUTION_STATE::is_txn_start() const {
  return (txn_status & TXN_START) != 0;
}

bool EXECUTION_STATE::is_singleStepping() const {
  return (mode & SSTEP) != 0;
}

bool EXECUTION_STATE::is_mixedMode() const {
  return (mode & MIXED) != 0;
}

// bounceback disabled in INTERP_ONLY mode and when SSTEP is set, will always be false (see constructor in Executor.h)
bool EXECUTION_STATE::is_bouncing() const {
  return (mode & BOUNCE) != 0;
}

bool EXECUTION_STATE::istate_none_of(uint16_t mask) const {
  return (istate & mask) == 0;
}

// check concreteness, transaction start, and update state based on abort type
void EXECUTION_STATE::update(ABORT_INFO::ABORT_TYPE type){
  //  LOG_TASE("Entering update with type \n");LOG_FLUSH();
  bool conc = (mode & MIXED) != 0 && !tase_buf_has_taint((void *) &target_ctx_gregs[0], TASE_NGREG * TASE_GREG_SIZE);
  
  bool start = (mode & SSTEP) != 0 || cartridge_entry_points.find(target_ctx_gregs[GREG_RIP].u64) != cartridge_entry_points.end();
  txn_status = (conc ? CONCRETE : 0) | (start ? TXN_START : 0);

  switch( type ){
  case ABORT_INFO::MODEL:
    istate = MODEL;
    break;
  case ABORT_INFO::POISON:       // this looks strange, but we want to try and bounce back if we have poison so that we clear the 
    if( (mode & SSTEP) != 0 ) {  // cartridges that did not have poison, then come back for the one that did
      istate = INTERP;
      break;
    }
    [[fallthrough]];    
  case ABORT_INFO::UNKNOWN:
    [[fallthrough]];
  case ABORT_INFO::OTHER:
    if( (mode & BOUNCE) != 0 ) {
      if( tran_max > 0 ) {
	istate = BOUNCEBACK;
	target_ctx_gregs[GREG_RIP].u64 -= bounceback_offset;
      } else {
	istate = FAULT;
      }
    }
  }
}

//Todo -- Add case for if regs aren't concrete, need istate to be INTERP
void EXECUTION_STATE::update(){
  //  LOG_TASE("Entering update  \n");LOG_FLUSH();
  bool conc = (mode & MIXED) != 0 && !tase_buf_has_taint((void *) &target_ctx_gregs[0], TASE_NGREG * TASE_GREG_SIZE);
  // if (conc) {
  //   LOG_TASE("conc is true \n");LOG_FLUSH();
  // } else {
  //   LOG_TASE("conc is false \n");LOG_FLUSH();
  // }
  bool start = (mode & SSTEP) != 0 || cartridge_entry_points.find(target_ctx_gregs[GREG_RIP].u64) != cartridge_entry_points.end();
  txn_status = (conc ? CONCRETE : 0) | (start ? TXN_START : 0);

  if( (mode & MIXED) != 0 && taseDebug > 0 ) {
    LOG_TASE("Inst %s transaction\n", start ? "begins" : "doesn't begin");
    LOG_TASE("Registers %s concrete\n", conc ? "are" : "aren't");
  }
  
  if( conc && start ) {
    //    LOG_TASE("Updating state to resume \n");LOG_FLUSH();
    istate = RESUME;
  }
  if (!conc) { //FIX added 05/06/2024 for poison in regs after modeled fn
    istate = INTERP;
  }
}


void ABORT_INFO::print_counts() const {
  LOG_TASE("BB_UNKNOWN: %d\n", counts.unknown)
  LOG_TASE("BB_MODEL: %d\n", counts.model)
  LOG_TASE("BB_POISON: %d\n", counts.poison)
  LOG_TASE("BB_OTHER: %d\n", counts.other)    
}


void ABORT_INFO::reset_counts(){
  counts = ABORT_COUNTS{0, 0, 0, 0};
}

extern void * __bss_start;
extern void * _end;
extern void * __data_start;

/*
  uint32_t abort_status: first bit is for xabort (or fake xabort)
  high 8 bits are for xabort return value 

  model abort is fake xabort with ff in high bits
  poison is xabort with 0-15 (0x00-0x0f - high bits
 */
extern "C" uint8_t tran_taint;
void ABORT_INFO::classify_and_count(){
  uint8_t high_bits = (uint8_t) ((target_ctx.abort_status & TSX_XABORT_MASK)>>24);
  bool tsx = target_ctx.abort_status & (1<<TSX_XABORT);  // caused by an explicit XABORT instr with some arg in high bits
  if( target_ctx.abort_status == 0 && taseDebug > 0 ) {

    LOG_TASE("Empty abort status at %lx, %d\n", target_ctx_gregs[GREG_RIP].u64, tran_taint);LOG_FLUSH();
  }
  bool retry = target_ctx.abort_status == 0 || (target_ctx.abort_status & 0xe) != 0; // 0x2 - could retry, 0x4 - log. processor conflict, 0x8 - overflow
  
  type = tsx ? ( high_bits == 0xff ? ABORT_TYPE::MODEL : (high_bits < 16) ?  ABORT_TYPE::POISON : ABORT_TYPE::UNKNOWN ) :
               high_bits == 0 ? ABORT_TYPE::UNKNOWN :
                                ABORT_TYPE::OTHER; 

  tran_max = (type & (ABORT_TYPE::UNKNOWN | ABORT_TYPE::OTHER)) == 0
    ? (type & ABORT_TYPE::POISON) == 0 ? tran_max : high_bits
    : ( retry ? tran_max/2 : 0 ); 

  value = target_ctx.abort_status & 0x1f;
  
  switch( type ){
  case ABORT_TYPE::MODEL:
    ex_state = EXECUTION_STATE::MODEL;
    counts.model++;
    break;
  case ABORT_TYPE::POISON:
    counts.poison++;
    break;
  case ABORT_TYPE::UNKNOWN:
    counts.unknown++;
    break;
  case ABORT_TYPE::OTHER:
    counts.other++;
    break;
  }
}


void ABORT_INFO::print() const {
  DBG_TASE("Abort type: ");
  switch( type ){
  case ABORT_TYPE::UNKNOWN:
    DBG_TASE("Unknown(%d)\n", value);
    break;
  case ABORT_TYPE::MODEL:
    DBG_TASE("Model(%d)\n", value);
    break;
  case ABORT_TYPE::POISON:
    DBG_TASE("Poison(%d)\n", value);
    break;
  case ABORT_TYPE::OTHER:
    DBG_TASE("Other/fallthrough(%d)\n", value);
    break;
  }
}



namespace klee {
  RNG theRNG;
  extern bool useLEARCHFeatsOracle;
}

const char *Executor::TerminateReasonNames[] = {
  [ Abort ] = "abort",
  [ Assert ] = "assert",
  [ BadVectorAccess ] = "bad_vector_access",
  [ Exec ] = "exec",
  [ External ] = "external",
  [ Free ] = "free",
  [ Model ] = "model",
  [ Overflow ] = "overflow",
  [ Ptr ] = "ptr",
  [ ReadOnly ] = "readonly",
  [ ReportError ] = "reporterror",
  [ User ] = "user",
  [ Unhandled ] = "xxx",
};


double interp_setup_time = 0.0;
double interp_find_fn_time = 0.0; //Should also account for interp_setup_time
double interp_run_time = 0.0;
double interp_cleanup_time = 0.0;
double interp_enter_time;
double interp_exit_time;
double solver_start_time;
double solver_end_time;
double solver_diff_time;

double run_start_time = 0;
double run_end_time = 0;

int run_interp_insts = 0;
int run_interp_traps = 0; //Number of traps to the interpreter
int run_model_count = 0; //Number of model calls
int run_bb_count = 0; //Number of basic blocks interpreted through

double run_model_time = 0;
double run_interp_time = 0;  //Total time in interpreter
double run_core_interp_time = 0; //Total time interpreting insts
double run_fork_time = 0;
double run_solver_time = 0;
double run_fault_time = 0;
double run_mem_op_time = 0;
double run_tmp_1_time = 0;
double run_tmp_2_time = 0;
double run_tmp_3_time = 0;
double mem_op_eval_time = 0;
double mo_resolve_time = 0;


void reset_run_timers() {

  run_start_time = util::getWallTime();
  interp_enter_time = util::getWallTime();

  run_interp_insts = 0;
  run_interp_traps = 0;
  run_model_count = 0;
  run_bb_count = 0;

  run_model_time = 0;
  run_interp_time = 0;
  run_core_interp_time = 0;
  run_fork_time = 0;
  run_solver_time = 0;
  run_fault_time =0;
  run_mem_op_time = 0;
  run_tmp_1_time = 0;
  run_tmp_2_time = 0;
  run_tmp_3_time = 0;
  mem_op_eval_time = 0;
  mo_resolve_time = 0;


  abort_info.reset_counts();
}

void print_run_timers() {
  LOG_TASE(" %lf seconds elapsed since target started \n", (util::getWallTime() - target_start_time))
  LOG_TASE(" --- Printing run timers ----\n")
  LOG_TASE("ID string is %s \n", worker_ID_stream.str().c_str())
  LOG_TASE("Curr Unique log ID is %s\n", curr_unique_log_ID.c_str())
  LOG_TASE("Prev Unique log ID is %s\n", prev_unique_log_ID.c_str())

    double totalRunTime =  util::getWallTime() - run_start_time;
  run_interp_time += (util::getWallTime() - interp_enter_time);
  LOG_TASE("Total basic blocks %d \n", run_interp_insts )
  LOG_TASE("Total run time    : %lf \n",  totalRunTime)
  LOG_TASE(" - Model time     : %lf \n", run_model_time)
  LOG_TASE(" - Interp time    : %lf \n", run_interp_time)
  LOG_TASE("       -Core      : %lf \n", run_core_interp_time)
  LOG_TASE("       -Solver    : %lf \n", run_solver_time)
  LOG_TASE("       -Fork      : %lf \n", run_fork_time )
  LOG_TASE("       -Fault time: %lf \n", run_fault_time)
  LOG_TASE("       -Mem op    : %lf \n", run_mem_op_time)
  LOG_TASE("       -TMP1 time : %lf \n", run_tmp_1_time)
  LOG_TASE("       -TMP2 time : %lf \n", run_tmp_2_time)
  LOG_TASE("       -TMP3 time : %lf \n", run_tmp_3_time)
  LOG_TASE("MEM OP TIME       : %lf \n", run_mem_op_time)
  LOG_TASE(" mem op eval args : %lf \n", mem_op_eval_time)
  LOG_TASE("   -mo_resolve_t  : %lf \n", mo_resolve_time)

  abort_info.reset_counts();

  FILE * logFile = fopen(curr_unique_log_ID.c_str(), "w+");
  fprintf(logFile, "Prev log name, Round, Pass, Total Runtime, Interp Time, Solver Time, Fork Time, Core Interp Time,TMP1, TMP2, TMP3, RUN INTERP TRAPS, RUN BB COUNT, RUN MODEL COUNT \n");
  fprintf(logFile, "%s, %d, %d,", prev_unique_log_ID.c_str(), round_count, pass_count);
  fprintf(logFile, " %lf, %lf, %lf, %lf, %d, %lf, %lf, %lf, %lf, %d, %d, %d \n", totalRunTime, run_interp_time, run_solver_time, run_fork_time, run_interp_insts, run_core_interp_time, run_tmp_1_time, run_tmp_2_time, run_tmp_3_time, run_interp_traps, run_bb_count, run_model_count);
  fclose(logFile);
}

std::string makeNewLogID () {
  static int logCtr = 0;
  logCtr++;
  std::stringstream stream;
  int i = getpid();
  stream << "LOG." << i << ".";
  struct timeval t;
  gettimeofday(&t, NULL);
  stream << t.tv_sec << "." << t.tv_usec << "." << logCtr;

  return stream.str();

}


#include <dirent.h>
#include <sys/resource.h>
int get_num_fds()
{
     int fd_count;
     char buf[64];
     struct dirent *dp;

     snprintf(buf, 64, "/proc/%i/fd/", getpid());

     fd_count = 0;
     DIR *dir = opendir(buf);
     if( dir == NULL )
       return -1;
     while ( (dp = readdir(dir)) != NULL ) {
          fd_count++;
     }
     closedir(dir);
     return fd_count;
}

void cycleTASELogs(bool isReplay) {
  if (isReplay) {
    prev_unique_log_ID = prev_worker_ID;
  } else {
    prev_unique_log_ID = curr_unique_log_ID;
  }
  curr_unique_log_ID = makeNewLogID();


  prev_worker_ID = worker_ID_stream.str();
  //  reset_run_timers();

  fflush(stdout);
  fflush(stderr);
  LOG_FLUSH();
  
  double T0 = util::getWallTime();
  int i = getpid();
  int j;
  worker_ID_stream >> j;
  worker_ID_stream << i;
   
  if ( j != i ) {
    int len = ftell(prev_stdout_log);
    //fclose(prev_stdout_log); // necessary?
    
    FILE *tmp = freopen(worker_ID_stream.str().c_str(), "w+", stdout);
    if( tmp == NULL ) {
      LOG_TASE("Error in freopen \"%s\": %d\n", worker_ID_stream.str().c_str(), errno);
      LOG_TASE("fd count: %d\n", get_num_fds());
      LOG_FLUSH();
      worker_error(Stopped, Running);
      exit(1);
    }
    
    if( len > 0 ) {

      prev_stdout_log = fopen(prev_worker_ID.c_str(), "r");

      if( tmp == NULL ) {
	LOG_TASE("tmp file is NULL");
      }
      if( prev_stdout_log == NULL ) {
	LOG_TASE("prev_stdout_log is NULL");
      }
      LOG_FLUSH();
      
      uint64_t bytes = sendfile(fileno(tmp), fileno(prev_stdout_log), NULL, len); // each stdout log starts with a copy of the previous
    
      fclose(prev_stdout_log);
    
      LOG_TASE("stdout bytes copied: %ld\nnew stdout filename: %s\n", bytes, worker_ID_stream.str().c_str())
      LOG_FLUSH()
    }
    
    prev_stdout_log = tmp;

    if( taseLog != NULL ) {
      fclose(taseLog);
      std::string mon = logFile + "." + std::to_string(i);
      taseLog = fopen(mon.c_str(), "w");
    }
  }

  double T1 = util::getWallTime();
  LOG_TASE("Spent %f seconds resetting log streams\nTime since start is %f\n", T1 - T0, util::getWallTime() - target_start_time);
  if (prev_stdout_log == NULL ) {
    LOG_TASE("ERROR opening new file for child process logging for pid %d\n", i)
    LOG_FLUSH()
    worker_error(Stopped, Running);
    exit(1);
  }
  
  run_interp_time = 0;
  interp_enter_time = util::getWallTime();
}


void measure_interp_time(uint64_t interpCtr_init, uint64_t rip) {

  double interp_exit_time = util::getWallTime();
  double diff_time = (interp_exit_time) - (interp_enter_time);
  run_interp_time += diff_time;

  if (target_ctx.abort_status == 0) {
    run_fault_time += diff_time;
  }

  LOG_TASE("Elapsed time is %lf at interpCtr %lu rip 0x%lx with %lu interpreter loops and abort code 0x%08x \n------------------------------\n", diff_time, interpCtr, rip, interpCtr - interpCtr_init, target_ctx.abort_status)
}


Executor::Executor(LLVMContext &ctx, const InterpreterOptions &opts,
    InterpreterHandler *ih)
    : Interpreter(opts), kmodule(0), interpreterHandler(ih), searcher(0),
      externalDispatcher(new ExternalDispatcher(ctx)), statsTracker(0),
      pathWriter(0), symPathWriter(0), specialFunctionHandler(0),
      processTree(0), replayKTest(0), replayPath(0), usingSeeds(0),
      atMemoryLimit(false), inhibitForking(false), haltExecution(false),
      ivcEnabled(false),
      coreSolverTimeout(MaxCoreSolverTime != 0 && MaxInstructionTime != 0
                            ? std::min(MaxCoreSolverTime, MaxInstructionTime)
                            : std::max(MaxCoreSolverTime, MaxInstructionTime)),
      debugInstFile(0), debugLogBuffer(debugBufferString) {

  if (coreSolverTimeout) UseForkedCoreSolver = true;
  Solver *coreSolver = klee::createCoreSolver(CoreSolverToUse);
  if (!coreSolver) {
    klee_error("Failed to create core solver\n");
  }

  Solver *solver = constructSolverChain(
      coreSolver,
      interpreterHandler->getOutputFilename(ALL_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_SMT2_FILE_NAME),
      interpreterHandler->getOutputFilename(ALL_QUERIES_KQUERY_FILE_NAME),
      interpreterHandler->getOutputFilename(SOLVER_QUERIES_KQUERY_FILE_NAME));

  this->solver = new TimingSolver(solver, EqualitySubstitution);
  memory = new MemoryManager(&arrayCache);

  initializeSearchOptions();

  if (DebugPrintInstructions.isSet(FILE_ALL) ||
      DebugPrintInstructions.isSet(FILE_COMPACT) ||
      DebugPrintInstructions.isSet(FILE_SRC)) {
    std::string debug_file_name =
        interpreterHandler->getOutputFilename("instructions.txt");
    std::string ErrorInfo;
#ifdef HAVE_ZLIB_H
    if (!DebugCompressInstructions) {
#endif

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 6)
    std::error_code ec;
    debugInstFile = new llvm::raw_fd_ostream(debug_file_name.c_str(), ec,
                                             llvm::sys::fs::OpenFlags::F_Text);
    if (ec)
	    ErrorInfo = ec.message();
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 5)
    debugInstFile = new llvm::raw_fd_ostream(debug_file_name.c_str(), ErrorInfo,
                                             llvm::sys::fs::OpenFlags::F_Text);
#else
    debugInstFile =
        new llvm::raw_fd_ostream(debug_file_name.c_str(), ErrorInfo);
#endif
#ifdef HAVE_ZLIB_H
    } else {
      debugInstFile = new compressed_fd_ostream(
          (debug_file_name + ".gz").c_str(), ErrorInfo);
    }
#endif
    if (ErrorInfo != "") {
      klee_error("Could not open file %s : %s", debug_file_name.c_str(),
                 ErrorInfo.c_str());
    }
  }
}


const Module *Executor::setModule(llvm::Module *module, 
                                  const ModuleOptions &opts) {
  
  assert (!kmodule && "kmodule fail \n");
  assert (module && "module fail \n");
  assert(!kmodule && module && "can only register one module"); // XXX gross
  kmodule = new KModule(module);
  // Initialize the context.
  DataLayout *TD = kmodule->targetData;
  Context::initialize(TD->isLittleEndian(),
                      (Expr::Width) TD->getPointerSizeInBits());
  specialFunctionHandler = new SpecialFunctionHandler(*this);

  specialFunctionHandler->prepare();
  kmodule->prepare(opts, interpreterHandler);
  specialFunctionHandler->bind();

  //Can't use the KLEE built in stats trackers because we fork a
  //process for each state in TASE.
  /*
  if (StatsTracker::useStatistics() || userSearcherRequiresMD2U()) {
    statsTracker = 
      new StatsTracker(*this,
                       interpreterHandler->getOutputFilename("assembly.ll"),
                       userSearcherRequiresMD2U());
  }
  */

  return module;
}

Executor::~Executor() {
  delete memory;
  delete externalDispatcher;
  delete processTree;
  delete specialFunctionHandler;
  delete statsTracker;
  delete solver;
  delete kmodule;
  while(!timers.empty()) {
    delete timers.back();
    timers.pop_back();
  }
  delete debugInstFile;
}

/***/

void Executor::initializeGlobalObject(ExecutionState &state, ObjectState *os,
                                      const Constant *c, 
                                      unsigned offset) {
  DataLayout *targetData = kmodule->targetData;
  if (const ConstantVector *cp = dyn_cast<ConstantVector>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(cp->getType()->getElementType());
    for (unsigned i=0, e=cp->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cp->getOperand(i), 
			     offset + i*elementSize);
  } else if (isa<ConstantAggregateZero>(c)) {
    unsigned i, size = targetData->getTypeStoreSize(c->getType());
    for (i=0; i<size; i++)
      os->write8(offset+i, (uint8_t) 0);
  } else if (const ConstantArray *ca = dyn_cast<ConstantArray>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(ca->getType()->getElementType());
    for (unsigned i=0, e=ca->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, ca->getOperand(i), 
			     offset + i*elementSize);
  } else if (const ConstantStruct *cs = dyn_cast<ConstantStruct>(c)) {
    const StructLayout *sl =
      targetData->getStructLayout(cast<StructType>(cs->getType()));
    for (unsigned i=0, e=cs->getNumOperands(); i != e; ++i)
      initializeGlobalObject(state, os, cs->getOperand(i), 
			     offset + sl->getElementOffset(i));
  } else if (const ConstantDataSequential *cds =
               dyn_cast<ConstantDataSequential>(c)) {
    unsigned elementSize =
      targetData->getTypeStoreSize(cds->getElementType());
    for (unsigned i=0, e=cds->getNumElements(); i != e; ++i)
      initializeGlobalObject(state, os, cds->getElementAsConstant(i),
                             offset + i*elementSize);
  } else if (!isa<UndefValue>(c)) {
    unsigned StoreBits = targetData->getTypeStoreSizeInBits(c->getType());
    ref<ConstantExpr> C = evalConstant(c);

    // Extend the constant if necessary;
    assert(StoreBits >= C->getWidth() && "Invalid store size!");
    if (StoreBits > C->getWidth())
      C = C->ZExt(StoreBits);

    os->write(offset, C);
  }
}

MemoryObject* Executor::addExternalObject(ExecutionState &state, 
                                           void *addr, unsigned size, 
                                           bool isReadOnly, const std::string& name, bool forTASE) {
  
  MemoryObject *mo = memory->allocateFixed((uint64_t) (unsigned long) addr, 
                                           size, 0);
  mo->setName(name);
  ObjectState *os = bindObjectInState(state, mo, false, NULL, forTASE);
  
  //printf("Mapping external buf: mo->address is 0x%lx, size is 0x%x \n", mo->address, size);
  os->concreteStore = (uint8_t *) mo->address;
  //for(unsigned i = 0; i < size; i++)
  // os->write8(i, ((uint8_t*)addr)[i]);
  if(isReadOnly)
    os->setReadOnly(true);  
  return mo;
}


bool Executor::addExternalObjectCheck(ExecutionState &state, 
                                           void *addr, unsigned size, 
                                           bool isReadOnly, const std::string& name, bool forTASE) {
  
  ObjectPair op;
  ref<ConstantExpr> CE = ConstantExpr::create((uint64_t) addr, Expr::Int64);
  if ( state.addressSpace.resolveOne(CE, op) ) {
    //    if ( taseDebug ) {
      //       std::cout << "mapped address resolved to MO: " << op.first->name << std::endl;
    //    }
    DBG_TASE("mapped address resolved to MO: %s\n", op.first->name.c_str())
    return false;
  }
  
  //  if ( taseDebug ) {
  //    std::cout << "no MO found, allocating" << std::endl;
  //  }
  DBG_TASE("no MO found, allocating\n")
  
  MemoryObject *mo = memory->allocateFixed((uint64_t) (unsigned long) addr, 
                                           size, 0);
  mo->setName(name);
  ObjectState *os = bindObjectInState(state, mo, false, NULL, forTASE);
  
  os->concreteStore = (uint8_t *) mo->address;

  if(isReadOnly)
    os->setReadOnly(true);
  
  return true;
}

  

extern void *__dso_handle __attribute__ ((__weak__));

void Executor::initializeGlobals(ExecutionState &state) {
  Module *m = kmodule->module;

  if (m->getModuleInlineAsm() != "")
    klee_warning("executable has module level assembly (ignoring)");
  // represent function globals using the address of the actual llvm function
  // object. given that we use malloc to allocate memory in states this also
  // ensures that we won't conflict. we don't need to allocate a memory object
  // since reading/writing via a function pointer is unsupported anyway.
  for (Module::iterator i = m->begin(), ie = m->end(); i != ie; ++i) {
    Function *f = &*i;
    ref<ConstantExpr> addr(0);

    // If the symbol has external weak linkage then it is implicitly
    // not defined in this module; if it isn't resolvable then it
    // should be null.
    if (f->hasExternalWeakLinkage() && 
        !externalDispatcher->resolveSymbol(f->getName())) {
      addr = Expr::createPointer(0);
    } else {
      addr = Expr::createPointer((unsigned long) (void*) f);
      legalFunctions.insert((uint64_t) (unsigned long) (void*) f);
    }
    
    globalAddresses.insert(std::make_pair(f, addr));
  }

  // Disabled, we don't want to promote use of live externals.
#ifdef HAVE_CTYPE_EXTERNALS
#ifndef WINDOWS
#ifndef DARWIN
  /* From /usr/include/errno.h: it [errno] is a per-thread variable. */
  int *errno_addr = __errno_location();
  addExternalObject(state, (void *)errno_addr, sizeof *errno_addr, false);

  /* from /usr/include/ctype.h:
       These point into arrays of 384, so they can be indexed by any `unsigned
       char' value [0,255]; by EOF (-1); or by any `signed char' value
       [-128,-1).  ISO C requires that the ctype functions work for `unsigned */
  const uint16_t **addr = __ctype_b_loc();
  addExternalObject(state, const_cast<uint16_t*>(*addr-128),
                    384 * sizeof **addr, true);
  addExternalObject(state, addr, sizeof(*addr), true);
    
  const int32_t **lower_addr = __ctype_tolower_loc();
  addExternalObject(state, const_cast<int32_t*>(*lower_addr-128),
                    384 * sizeof **lower_addr, true);
  addExternalObject(state, lower_addr, sizeof(*lower_addr), true);
  
  const int32_t **upper_addr = __ctype_toupper_loc();
  addExternalObject(state, const_cast<int32_t*>(*upper_addr-128),
                    384 * sizeof **upper_addr, true);
  addExternalObject(state, upper_addr, sizeof(*upper_addr), true);
#endif
#endif
#endif

  // allocate and initialize globals, done in two passes since we may
  // need address of a global in order to initialize some other one.

  // allocate memory objects for all globals
  for (Module::const_global_iterator i = m->global_begin(),
         e = m->global_end();
       i != e; ++i) {
    const GlobalVariable *v = &*i;
    size_t globalObjectAlignment = getAllocationAlignment(v);
    if (i->isDeclaration()) {
      // FIXME: We have no general way of handling unknown external
      // symbols. If we really cared about making external stuff work
      // better we could support user definition, or use the EXE style
      // hack where we check the object file information.

      Type *ty = i->getType()->getElementType();
      uint64_t size = 0;
      if (ty->isSized()) {
	size = kmodule->targetData->getTypeStoreSize(ty);
      } else {
        klee_warning("Type for %.*s is not sized", (int)i->getName().size(),
			i->getName().data());
      }

      // XXX - DWD - hardcode some things until we decide how to fix.
#ifndef WINDOWS
      if (i->getName() == "_ZTVN10__cxxabiv117__class_type_infoE") {
        size = 0x2C;
      } else if (i->getName() == "_ZTVN10__cxxabiv120__si_class_type_infoE") {
        size = 0x2C;
      } else if (i->getName() == "_ZTVN10__cxxabiv121__vmi_class_type_infoE") {
        size = 0x2C;
      }
#endif

      if (size == 0) {
        klee_warning("Unable to find size for global variable: %.*s (use will result in out of bounds access)",
			(int)i->getName().size(), i->getName().data());
      }

      MemoryObject *mo = memory->allocate(size, /*isLocal=*/false,
                                          /*isGlobal=*/true, /*allocSite=*/v,
                                          /*alignment=*/globalObjectAlignment);
      ObjectState *os = bindObjectInState(state, mo, false);
      globalObjects.insert(std::make_pair(v, mo));
      globalAddresses.insert(std::make_pair(v, mo->getBaseExpr()));

      // Program already running = object already initialized.  Read
      // concrete value and write it to our copy.
      if (size) {
        void *addr;
        if (i->getName() == "__dso_handle") {
          addr = &__dso_handle; // wtf ?
        } else {
          addr = externalDispatcher->resolveSymbol(i->getName());
        }
        if (!addr)
          klee_error("unable to load symbol(%s) while initializing globals.", 
                     i->getName().data());

        for (unsigned offset=0; offset<mo->size; offset++){
          os->write8(offset, ((unsigned char*)addr)[offset]);
	}
      }
    } else {
      Type *ty = i->getType()->getElementType();
      uint64_t size = kmodule->targetData->getTypeStoreSize(ty);
      MemoryObject *mo = memory->allocate(size, /*isLocal=*/false,
                                          /*isGlobal=*/true, /*allocSite=*/v,
                                          /*alignment=*/globalObjectAlignment);
      if (!mo)
        llvm::report_fatal_error("out of memory");
      ObjectState *os = bindObjectInState(state, mo, false);
      globalObjects.insert(std::make_pair(v, mo));
      globalAddresses.insert(std::make_pair(v, mo->getBaseExpr()));

      if (!i->hasInitializer())
          os->initializeToRandom();
    }
  }
  
  // link aliases to their definitions (if bound)
  for (Module::alias_iterator i = m->alias_begin(), ie = m->alias_end(); 
       i != ie; ++i) {
    // Map the alias to its aliasee's address. This works because we have
    // addresses for everything, even undefined functions. 
    globalAddresses.insert(std::make_pair(&*i, evalConstant(i->getAliasee())));
  }

  // once all objects are allocated, do the actual initialization
  for (Module::const_global_iterator i = m->global_begin(),
         e = m->global_end();
       i != e; ++i) {
    if (i->hasInitializer()) {
      const GlobalVariable *v = &*i;
      MemoryObject *mo = globalObjects.find(v)->second;
      const ObjectState *os = state.addressSpace.findObject(mo);
      assert(os);
      ObjectState *wos = state.addressSpace.getWriteable(mo, os);
      
      initializeGlobalObject(state, wos, i->getInitializer(), 0);
      // if(i->isConstant()) os->setReadOnly(true);
    }
  }
}

void Executor::branch(ExecutionState &state, 
                      const std::vector< ref<Expr> > &conditions,
                      std::vector<ExecutionState*> &result) {
  TimerStatIncrementer timer(stats::forkTime);
  unsigned N = conditions.size();
  assert(N);

  if (MaxForks!=~0u && stats::forks >= MaxForks) {
    unsigned next = theRNG.getInt32() % N;
    for (unsigned i=0; i<N; ++i) {
      if (i == next) {
        result.push_back(&state);
      } else {
        result.push_back(NULL);
      }
    }
  } else {
    stats::forks += N-1;

    // XXX do proper balance or keep random?
    result.push_back(&state);
    for (unsigned i=1; i<N; ++i) {
      ExecutionState *es = result[theRNG.getInt32() % i];
      ExecutionState *ns = es->branch();
      addedStates.push_back(ns);
      result.push_back(ns);
      es->ptreeNode->data = 0;
      std::pair<PTree::Node*,PTree::Node*> res = 
        processTree->split(es->ptreeNode, ns, es);
      ns->ptreeNode = res.first;
      es->ptreeNode = res.second;
    }
  }

  // If necessary redistribute seeds to match conditions, killing
  // states if necessary due to OnlyReplaySeeds (inefficient but
  // simple).
  
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&state);
  if (it != seedMap.end()) {
    std::vector<SeedInfo> seeds = it->second;
    seedMap.erase(it);

    // Assume each seed only satisfies one condition (necessarily true
    // when conditions are mutually exclusive and their conjunction is
    // a tautology).
    for (std::vector<SeedInfo>::iterator siit = seeds.begin(), 
           siie = seeds.end(); siit != siie; ++siit) {
      unsigned i;
      for (i=0; i<N; ++i) {
        ref<ConstantExpr> res;
        bool success = 
          solver->getValue(state, siit->assignment.evaluate(conditions[i]), 
                           res);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (res->isTrue())
          break;
      }
      
      // If we didn't find a satisfying condition randomly pick one
      // (the seed will be patched).
      if (i==N)
        i = theRNG.getInt32() % N;

      // Extra check in case we're replaying seeds with a max-fork
      if (result[i])
        seedMap[result[i]].push_back(*siit);
    }

    if (OnlyReplaySeeds) {
      for (unsigned i=0; i<N; ++i) {
        if (result[i] && !seedMap.count(result[i])) {
          terminateState(*result[i]);
          result[i] = NULL;
        }
      } 
    }
  }

  for (unsigned i=0; i<N; ++i)
    if (result[i])
      addConstraint(*result[i], conditions[i]);
}

extern std::vector<double> round_constraint_features;

Executor::StatePair 
Executor::fork(ExecutionState &current, ref<Expr> condition, bool isInternal) {  
  double f_start = util::getWallTime();

  //  printf("Entering regular klee fork() \n");fflush(stdout);
  // if (taseDebug) {
  //   outs() << "Condition in regular klee fork is \n";
  //   condition->dumpToStdout();
  //   outs().flush();
  // }
  Solver::Validity res;
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&current);
  bool isSeeding = it != seedMap.end();
  double timeout = coreSolverTimeout;
  if (isSeeding)
    timeout *= it->second.size();
  solver->setTimeout(timeout);

  if (!isa<ConstantExpr> (condition)) {
    //    printf("DEBUG:FORK ctx is \n");
    //LOG_TASE("DEBUG:FORK ctx is \n")
      //printCtx();
    forkSolverCalls++;
  }
  
  LOG_TASE("Calling solver->evaluate in ugly case \n");
  double evalStart = util::getWallTime();
  bool success = solver->evaluate(current, condition, res);
  LOG_TASE("%lf seconds elapsed in evalStart \n", util::getWallTime() - evalStart);
  solver->setTimeout(0);
  if (!success) {
    //    printf("INTERPRETER: QUERY TIMEOUT \n");
    LOG_TASE("INTERPRETER: QUERY TIMEOUT \n");
    current.pc = current.prevPC;
    terminateStateEarly(current, "Query timed out (fork).");
    LOG_TASE("%lf seconds elapsed in forkUgly \n", util::getWallTime() - f_start);
    return StatePair(0, 0);
  }

  //Either condition is always true, always false, or we need to fork.
  if (res==Solver::True) {
    //    if (taseDebug) {
      //      printf("DEBUG:FORK - Solver returned true \n");
    //      std::cout.flush();
    //    }
    DBG_TASE("FORK - Solver returned true \n");
    return StatePair(&current, 0);
  } else if (res==Solver::False) {
    //    if (taseDebug) {
    //      printf("Debug:FORK - Solver returned false \n");
    //      std::cout.flush();
    //    }
    DBG_TASE("FORK - Solver returned false \n");
    return StatePair(0, &current);
  } else {
    TimerStatIncrementer timer(stats::forkTime);
    //    ExecutionState *falseState, *trueState = &current;

    ++stats::forks;

    //    if ( taseDebug ) {
    //      std::cout << "tase_fork call in Executor::fork" << std::endl;
    //    }
    DBG_TASE("tase_fork call in Executor::fork");
    //ABH: This, along with "forkOnPossibleRIPValues", is one of
    //the two places we fork during path exploration in TASE.
    //    int parentPID = getpid();
    //    uint64_t rip = target_ctx_gregs[GREG_RIP].u64;
    //    int pid  = tase_fork(parentPID, rip);

      //int pid = worker_fork(Stopped, Running);
    LOG_TASE("%lf seconds since eval started \n", util::getWallTime() - postInitStartTime);
    LOG_TASE("spent %lf seconds in core interp coreinterpdbg IR case\n", util::getWallTime() - coreInterpStartTime);
    double IRForkTime = util::getWallTime();

    //PUH

    std::vector<std::vector<float>> IR_Constraint_BOWs;

    if (klee::useLEARCHFeatsOracle) {
      LOG_TASE("Adding constraint features for IR case \n");LOG_FLUSH();
      addConstraintFeature(Expr::createIsZero(condition));
      std::vector<float> false_constraint_bows;
      //float false_constraint_bows[32];
      for (int i = 0; i < 32; i++) {
	//false_constraint_bows[i] = (float) round_constraint_features[i];
	false_constraint_bows.push_back((float) round_constraint_features[i]);
      }
      IR_Constraint_BOWs.push_back(false_constraint_bows);
      remConstraintFeature(Expr::createIsZero(condition));
      
      
      addConstraintFeature(condition);
      //float true_constraint_bows[32];
      std::vector<float> true_constraint_bows;
      for (int i = 0; i < 32; i++) {
	true_constraint_bows.push_back((float) round_constraint_features[i]);
	//true_constraint_bows[i] = (float) round_constraint_features[i];
      }
      IR_Constraint_BOWs.push_back(true_constraint_bows);
      remConstraintFeature(condition);
    }
    
      
    int pid = forkOnPossibleIRBranches(condition, IR_Constraint_BOWs); //This should really just return true/false
    LOG_TASE("Spent %lf seconds on forkOnPossibleIRValues \n", util::getWallTime() - IRForkTime);
    coreInterpStartTime = util::getWallTime();
    
    if (pid == 0 ) {      
      addConstraint(*GlobalExecutionStatePtr, Expr::createIsZero(condition));
    } else {
      addConstraint(*GlobalExecutionStatePtr, condition);
    }

   
    
    //Call to solver to make sure we're legit on this branch.
    //    printf("Calling solver for sanity check \n");

    //ABH Removed on 04292024.  This check below should be redundant based on the logic in
    //forkOnPossibleIRBranches() checking the validity of each branch.  Double check.
    /*
    LOG_TASE("Calling solver for sanity check \n")

    std::vector< std::vector<unsigned char> > values;
    std::vector<const Array*> objects;
    for (unsigned i = 0; i != GlobalExecutionStatePtr->symbolics.size(); ++i)
      objects.push_back(GlobalExecutionStatePtr->symbolics[i].second);
    bool success = solver->getInitialValues(*GlobalExecutionStatePtr, objects, values);
    if (success) {
      //      printf("Solver checked sanity \n");
      LOG_TASE("Solver checked sanity \n")
	} else {
      //      printf("Solver found invalid path \n");
      LOG_TASE("Solver found invalid path \n")
      printCtx();
      }*/

    if (pid == 0)  {
      LOG_TASE("%lf seconds elapsed in forkUgly \n", util::getWallTime() - f_start);LOG_FLUSH();
      return StatePair(0, GlobalExecutionStatePtr);
    } else {
      LOG_TASE("%lf seconds elapsed in forkUgly \n", util::getWallTime() - f_start);LOG_FLUSH();
      return StatePair(GlobalExecutionStatePtr,0);
    }
  }
}

void Executor::addConstraint(ExecutionState &state, ref<Expr> condition) {

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(condition)) {
    if (!CE->isTrue())
      llvm::report_fatal_error("attempt to add invalid constraint");
    return;
  }

  // Check to see if this constraint violates seeds.
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&state);
  if (it != seedMap.end()) {
    bool warn = false;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(), 
           siie = it->second.end(); siit != siie; ++siit) {
      bool res;
      bool success = 
        solver->mustBeFalse(state, siit->assignment.evaluate(condition), res);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res) {
        siit->patchSeed(state, condition, solver);
        warn = true;
      }
    }
    if (warn)
      klee_warning("seeds patched for violating constraint"); 
  }


  state.addConstraint(condition);

  
  if (ivcEnabled)
    doImpliedValueConcretization(state, condition, 
                                 ConstantExpr::alloc(1, Expr::Bool));


}

const Cell& Executor::eval(KInstruction *ki, unsigned index, 
                           ExecutionState &state) const {
  assert(index < ki->inst->getNumOperands());
  int vnumber = ki->operands[index];

  assert(vnumber != -1 &&
         "Invalid operand to eval(), not a value or constant!");

  // Determine if this is a constant or not.
  if (vnumber < 0) {
    unsigned index = -vnumber - 2;
    return kmodule->constantTable[index];
  } else {
    unsigned index = vnumber;
    StackFrame &sf = state.stack.back();
    return sf.locals[index];
  }
}

void Executor::bindLocal(KInstruction *target, ExecutionState &state, 
                         ref<Expr> value) {
  getDestCell(state, target).value = value;
}

void Executor::bindArgument(KFunction *kf, unsigned index, 
                            ExecutionState &state, ref<Expr> value) {
  getArgumentCell(state, kf, index).value = value;
}

ref<Expr> Executor::toUnique(const ExecutionState &state, 
                             ref<Expr> &e) {

  //e->dump();
  ref<Expr> result = e;

  if (!isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool isTrue = false;

    solver->setTimeout(coreSolverTimeout);      
    if (solver->getValue(state, e, value) &&
        solver->mustBeTrue(state, EqExpr::create(e, value), isTrue) &&
        isTrue)
      result = value;
    solver->setTimeout(0);
  }
  
  return result;
}


/* Concretize the given expression, and return a possible constant value. 
   'reason' is just a documentation string stating the reason for concretization. */
ref<klee::ConstantExpr> 
Executor::toConstant(ExecutionState &state, 
                     ref<Expr> e,
                     const char *reason) {
  e = state.constraints.simplifyExpr(e);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e))
    return CE;

  ref<ConstantExpr> value;
  bool success = solver->getValue(state, e, value);
  assert(success && "FIXME: Unhandled solver failure");
  (void) success;

  std::string str;
  llvm::raw_string_ostream os(str);
  os << "silently concretizing (reason: " << reason << ") expression " << e
     << " to value " << value << " (" << (*(state.pc)).info->file << ":"
     << (*(state.pc)).info->line << ")";

  if (AllExternalWarnings)
    klee_warning(reason, os.str().c_str());
  else
    klee_warning_once(reason, "%s", os.str().c_str());

  addConstraint(state, EqExpr::create(e, value));
    
  return value;
}

void Executor::executeGetValue(ExecutionState &state,
                               ref<Expr> e,
                               KInstruction *target) {
  e = state.constraints.simplifyExpr(e);
  std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it = 
    seedMap.find(&state);
  if (it==seedMap.end() || isa<ConstantExpr>(e)) {
    ref<ConstantExpr> value;
    bool success = solver->getValue(state, e, value);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    bindLocal(target, state, value);
  } else {
    std::set< ref<Expr> > values;
    for (std::vector<SeedInfo>::iterator siit = it->second.begin(), 
           siie = it->second.end(); siit != siie; ++siit) {
      ref<ConstantExpr> value;
      bool success = 
        solver->getValue(state, siit->assignment.evaluate(e), value);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      values.insert(value);
    }
    
    std::vector< ref<Expr> > conditions;
    for (std::set< ref<Expr> >::iterator vit = values.begin(), 
           vie = values.end(); vit != vie; ++vit)
      conditions.push_back(EqExpr::create(e, *vit));

    std::vector<ExecutionState*> branches;
    branch(state, conditions, branches);
    
    std::vector<ExecutionState*>::iterator bit = branches.begin();
    for (std::set< ref<Expr> >::iterator vit = values.begin(), 
           vie = values.end(); vit != vie; ++vit) {
      ExecutionState *es = *bit;
      if (es)
        bindLocal(target, *es, *vit);
      ++bit;
    }
  }
}

void Executor::printDebugInstructions(ExecutionState &state) {
  // check do not print
  if (DebugPrintInstructions.getBits() == 0)
	  return;

  llvm::raw_ostream *stream = 0;
  if (DebugPrintInstructions.isSet(STDERR_ALL) ||
      DebugPrintInstructions.isSet(STDERR_SRC) ||
      DebugPrintInstructions.isSet(STDERR_COMPACT))
    stream = &llvm::errs();
  else
    stream = &debugLogBuffer;

  if (!DebugPrintInstructions.isSet(STDERR_COMPACT) &&
      !DebugPrintInstructions.isSet(FILE_COMPACT)) {
    (*stream) << "     ";
    state.pc->printFileLine(*stream);
    (*stream) << ":";
  }

  (*stream) << state.pc->info->assemblyLine;

  if (DebugPrintInstructions.isSet(STDERR_ALL) ||
      DebugPrintInstructions.isSet(FILE_ALL))
    (*stream) << ":" << *(state.pc->inst);
  (*stream) << "\n";

  if (DebugPrintInstructions.isSet(FILE_ALL) ||
      DebugPrintInstructions.isSet(FILE_COMPACT) ||
      DebugPrintInstructions.isSet(FILE_SRC)) {
    debugLogBuffer.flush();
    (*debugInstFile) << debugLogBuffer.str();
    debugBufferString = "";
  }
}

void Executor::stepInstruction(ExecutionState &state) {
  ++stats::instructions;
  state.prevPC = state.pc;
  ++state.pc;

  if (stats::instructions==StopAfterNInstructions)
    haltExecution = true;
}

void Executor::executeCall(ExecutionState &state, 
                           KInstruction *ki,
                           Function *f,
                           std::vector< ref<Expr> > &arguments) {
  Instruction *i = ki->inst;
  if (f && f->isDeclaration()) {
    switch(f->getIntrinsicID()) {
    case Intrinsic::not_intrinsic:
      // state may be destroyed by this call, cannot touch
      callExternalFunction(state, ki, f, arguments);
      break;
        
      // va_arg is handled by caller and intrinsic lowering, see comment for
      // ExecutionState::varargs
      case Intrinsic::vastart:  {
      printf("va_start encountered\n");
      fflush(stdout);
      StackFrame &sf = state.stack.back();

      // varargs can be zero if no varargs were provided
      if (!sf.varargs)
        return;

      // FIXME: This is really specific to the architecture, not the pointer
      // size. This happens to work for x86-32 and x86-64, however.
      Expr::Width WordSize = Context::get().getPointerWidth();
      if (WordSize == Expr::Int32) {
        executeMemoryOperation(state, true, arguments[0], 
                               sf.varargs->getBaseExpr(), 0, "vastart 0, instCtr: " + std::to_string(instCtr));
      } else {
        assert(WordSize == Expr::Int64 && "Unknown word size!");

        // x86-64 has quite complicated calling convention. However,
        // instead of implementing it, we can do a simple hack: just
        // make a function believe that all varargs are on stack.
        executeMemoryOperation(state, true, arguments[0],
                               ConstantExpr::create(48, 32), 0, "vastart 1, instCtr: " + std::to_string(instCtr)); // gp_offset
        executeMemoryOperation(state, true,
                               AddExpr::create(arguments[0], 
                                               ConstantExpr::create(4, 64)),
                               ConstantExpr::create(304, 32), 0, "vastart 2, instCtr: " + std::to_string(instCtr)); // fp_offset
        executeMemoryOperation(state, true,
                               AddExpr::create(arguments[0], 
                                               ConstantExpr::create(8, 64)),
                               sf.varargs->getBaseExpr(), 0, "vastart 3, instCtr: " + std::to_string(instCtr)); // overflow_arg_area
        executeMemoryOperation(state, true,
                               AddExpr::create(arguments[0], 
                                               ConstantExpr::create(16, 64)),
                               ConstantExpr::create(0, 64), 0, "vastart 4, instCtr: " + std::to_string(instCtr)); // reg_save_area
      }
      break;
    }
    case Intrinsic::vaend:
      // va_end is a noop for the interpreter.
      //
      // FIXME: We should validate that the target didn't do something bad
      // with va_end, however (like call it twice).
      break;
        
    case Intrinsic::vacopy:
      // va_copy should have been lowered.
      //
      // FIXME: It would be nice to check for errors in the usage of this as
      // well.
    default:
      klee_error("unknown intrinsic: %s", f->getName().data());
    }

    if (InvokeInst *ii = dyn_cast<InvokeInst>(i))
      transferToBasicBlock(ii->getNormalDest(), i->getParent(), state);
  } else {
    // FIXME: I'm not really happy about this reliance on prevPC but it is ok, I
    // guess. This just done to avoid having to pass KInstIterator everywhere
    // instead of the actual instruction, since we can't make a KInstIterator
    // from just an instruction (unlike LLVM).
    KFunction *kf = kmodule->functionMap[f];
    state.pushFrame(state.prevPC, kf);
    state.pc = kf->instructions;

    if (statsTracker)
      statsTracker->framePushed(state, &state.stack[state.stack.size()-2]);

     // TODO: support "byval" parameter attribute
     // TODO: support zeroext, signext, sret attributes

    unsigned callingArgs = arguments.size();
    unsigned funcArgs = f->arg_size();
    if (!f->isVarArg()) {
      if (callingArgs > funcArgs) {
        klee_warning_once(f, "calling %s with extra arguments.", 
                          f->getName().data());
      } else if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments",
                              User);
        return;
      }
    } else {
      printf("setting up varargs\n");
      fflush(stdout);
      Expr::Width WordSize = Context::get().getPointerWidth();

      if (callingArgs < funcArgs) {
        terminateStateOnError(state, "calling function with too few arguments",
                              User);
        return;
      }

      StackFrame &sf = state.stack.back();
      unsigned size = 0;
      bool requires16ByteAlignment = false;
      for (unsigned i = funcArgs; i < callingArgs; i++) {
        // FIXME: This is really specific to the architecture, not the pointer
        // size. This happens to work for x86-32 and x86-64, however.
        if (WordSize == Expr::Int32) {
          size += Expr::getMinBytesForWidth(arguments[i]->getWidth());
        } else {
          Expr::Width argWidth = arguments[i]->getWidth();
          // AMD64-ABI 3.5.7p5: Step 7. Align l->overflow_arg_area upwards to a
          // 16 byte boundary if alignment needed by type exceeds 8 byte
          // boundary.
          //
          // Alignment requirements for scalar types is the same as their size
          if (argWidth > Expr::Int64) {
             size = llvm::RoundUpToAlignment(size, 16);
             requires16ByteAlignment = true;
          }
          size += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
        }
      }

      MemoryObject *mo = sf.varargs =
          memory->allocate(size, true, false, state.prevPC->inst,
                           (requires16ByteAlignment ? 16 : 8));
      if (!mo && size) {
        terminateStateOnExecError(state, "out of memory (varargs)");
        return;
      }

      if (mo) {
        if ((WordSize == Expr::Int64) && (mo->address & 15) &&
            requires16ByteAlignment) {
          // Both 64bit Linux/Glibc and 64bit MacOSX should align to 16 bytes.
          klee_warning_once(
              0, "While allocating varargs: malloc did not align to 16 bytes.");
        }

        ObjectState *os = bindObjectInState(state, mo, true);
        unsigned offset = 0;
        for (unsigned i = funcArgs; i < callingArgs; i++) {
          // FIXME: This is really specific to the architecture, not the pointer
          // size. This happens to work for x86-32 and x86-64, however.
          if (WordSize == Expr::Int32) {
            os->write(offset, arguments[i]);
            offset += Expr::getMinBytesForWidth(arguments[i]->getWidth());
          } else {
            assert(WordSize == Expr::Int64 && "Unknown word size!");

            Expr::Width argWidth = arguments[i]->getWidth();
            if (argWidth > Expr::Int64) {
              offset = llvm::RoundUpToAlignment(offset, 16);
            }
            os->write(offset, arguments[i]);
            offset += llvm::RoundUpToAlignment(argWidth, WordSize) / 8;
          }
        }
      }
    }

    unsigned numFormals = f->arg_size();
    for (unsigned i=0; i<numFormals; ++i) 
      bindArgument(kf, i, state, arguments[i]);
  }
}

void Executor::transferToBasicBlock(BasicBlock *dst, BasicBlock *src, 
                                    ExecutionState &state) {
  // Note that in general phi nodes can reuse phi values from the same
  // block but the incoming value is the eval() result *before* the
  // execution of any phi nodes. this is pathological and doesn't
  // really seem to occur, but just in case we run the PhiCleanerPass
  // which makes sure this cannot happen and so it is safe to just
  // eval things in order. The PhiCleanerPass also makes sure that all
  // incoming blocks have the same order for each PHINode so we only
  // have to compute the index once.
  //
  // With that done we simply set an index in the state so that PHI
  // instructions know which argument to eval, set the pc, and continue.
  
  // XXX this lookup has to go ?
  KFunction *kf = state.stack.back().kf;
  unsigned entry = kf->basicBlockEntry[dst];
  state.pc = &kf->instructions[entry];


  if (state.pc->inst->getOpcode() == Instruction::PHI) {
    PHINode *first = static_cast<PHINode*>(state.pc->inst);
    state.incomingBBIndex = first->getBasicBlockIndex(src);
  }
}

/// Compute the true target of a function call, resolving LLVM and KLEE aliases
/// and bitcasts.
Function* Executor::getTargetFunction(Value *calledVal, ExecutionState &state) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 6)
      if (!Visited.insert(gv).second)
        return 0;
#else
      if (!Visited.insert(gv))
        return 0;
#endif
      std::string alias = state.getFnAlias(gv->getName());
      if (alias != "") {
        llvm::Module* currModule = kmodule->module;
        GlobalValue *old_gv = gv;
        gv = currModule->getNamedValue(alias);
        if (!gv) {
          klee_error("Function %s(), alias for %s not found!\n", alias.c_str(),
                     old_gv->getName().str().c_str());
        }
      }
     
      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
}

/// TODO remove?
static bool isDebugIntrinsic(const Function *f, KModule *KM) {
  return false;
}

static inline const llvm::fltSemantics * fpWidthToSemantics(unsigned width) {
  switch(width) {
  case Expr::Int32:
    return &llvm::APFloat::IEEEsingle;
  case Expr::Int64:
    return &llvm::APFloat::IEEEdouble;
  case Expr::Fl80:
    return &llvm::APFloat::x87DoubleExtended;
  default:
    return 0;
  }
}

void Executor::executeInstruction(ExecutionState &state, KInstruction *ki) {

  instCtr++;
  Instruction *i = ki->inst;
  switch (i->getOpcode()) {
    // Control flow
  case Instruction::Ret: {
    ReturnInst *ri = cast<ReturnInst>(i);
    KInstIterator kcaller = state.stack.back().caller;
    Instruction *caller = kcaller ? kcaller->inst : 0;
    bool isVoidReturn = (ri->getNumOperands() == 0);
    ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);
    
    if (!isVoidReturn) {
      result = eval(ki, 0, state).value;
    }
    
    if (state.stack.size() <= 1) {
      assert(!caller && "caller set on initial stack frame");
      //printf("Choosing not to call terminateStateOnExit(state) \n \n ");
      //terminateStateOnExit(state);
      state.popFrame();
      
      haltExecution = true;
      break;
    } else {
      state.popFrame();

      if (statsTracker)
        statsTracker->framePopped(state);
      if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
        transferToBasicBlock(ii->getNormalDest(), caller->getParent(), state);
      } else {
        state.pc = kcaller;
        ++state.pc;
      }

      if (!isVoidReturn) {
        Type *t = caller->getType();
        if (t != Type::getVoidTy(i->getContext())) {
          // may need to do coercion due to bitcasts
          Expr::Width from = result->getWidth();
          Expr::Width to = getWidthForLLVMType(t);
            
          if (from != to) {
            CallSite cs = (isa<InvokeInst>(caller) ? CallSite(cast<InvokeInst>(caller)) : 
                           CallSite(cast<CallInst>(caller)));

            // XXX need to check other param attrs ?
      bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
            if (isSExt) {
              result = SExtExpr::create(result, to);
            } else {
              result = ZExtExpr::create(result, to);
            }
          }

          bindLocal(kcaller, state, result);
        }
      } else {
        // We check that the return value has no users instead of
        // checking the type, since C defaults to returning int for
        // undeclared functions.
        if (!caller->use_empty()) {
          terminateStateOnExecError(state, "return void when caller expected a result");
        }
      }
    }
    
    break;
  }
  case Instruction::Br: {

    BranchInst *bi = cast<BranchInst>(i);
    if (bi->isUnconditional()) {
      transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
    } else {
      // FIXME: Find a way that we don't have this hidden dependency.
      assert(bi->getCondition() == bi->getOperand(0) &&
             "Wrong operand index!");
      ref<Expr> cond = eval(ki, 0, state).value;

      //ABH: Within TASE, we're unix forking within Executor::fork
      // when a branch instruction depends on symbolic data.  Currently
      // only ever returning 1 state in "branches" becuase of this.
      //printf("Br llvm instruction calling fork \n");fflush(stdout);
      Executor::StatePair branches = fork(state, cond, false);

      // NOTE: There is a hidden dependency here, markBranchVisited
      // requires that we still be in the context of the branch
      // instruction (it reuses its statistic id). Should be cleaned
      // up with convenient instruction specific data.
      if (statsTracker && state.stack.back().kf->trackCoverage)
        statsTracker->markBranchVisited(branches.first, branches.second);

      if (branches.second) {
        transferToBasicBlock(bi->getSuccessor(1), bi->getParent(), *branches.second);	
      }
      if (branches.first) {
        transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), *branches.first);
      }
            
    }
    break;
  }
  case Instruction::Switch: {
    SwitchInst *si = cast<SwitchInst>(i);
    ref<Expr> cond = eval(ki, 0, state).value;
    BasicBlock *bb = si->getParent();

    cond = toUnique(state, cond);
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
      // Somewhat gross to create these all the time, but fine till we
      // switch to an internal rep.
      llvm::IntegerType *Ty = cast<IntegerType>(si->getCondition()->getType());
      ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
      unsigned index = si->findCaseValue(ci).getSuccessorIndex();
      transferToBasicBlock(si->getSuccessor(index), si->getParent(), state);
    } else {
      // Handle possible different branch targets

      // We have the following assumptions:
      // - each case value is mutual exclusive to all other values including the
      //   default value
      // - order of case branches is based on the order of the expressions of
      //   the scase values, still default is handled last
      std::vector<BasicBlock *> bbOrder;
      std::map<BasicBlock *, ref<Expr> > branchTargets;

      std::map<ref<Expr>, BasicBlock *> expressionOrder;

      // Iterate through all non-default cases and order them by expressions
      for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end(); i != e;
           ++i) {
        ref<Expr> value = evalConstant(i.getCaseValue());

        BasicBlock *caseSuccessor = i.getCaseSuccessor();
        expressionOrder.insert(std::make_pair(value, caseSuccessor));
      }

      // Track default branch values
      ref<Expr> defaultValue = ConstantExpr::alloc(1, Expr::Bool);

      // iterate through all non-default cases but in order of the expressions
      for (std::map<ref<Expr>, BasicBlock *>::iterator
               it = expressionOrder.begin(),
               itE = expressionOrder.end();
           it != itE; ++it) {
        ref<Expr> match = EqExpr::create(cond, it->first);

        // Make sure that the default value does not contain this target's value
        defaultValue = AndExpr::create(defaultValue, Expr::createIsZero(match));

        // Check if control flow could take this case
        bool result;
        bool success = solver->mayBeTrue(state, match, result);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        if (result) {
          BasicBlock *caseSuccessor = it->second;

          // Handle the case that a basic block might be the target of multiple
          // switch cases.
          // Currently we generate an expression containing all switch-case
          // values for the same target basic block. We spare us forking too
          // many times but we generate more complex condition expressions
          // TODO Add option to allow to choose between those behaviors
          std::pair<std::map<BasicBlock *, ref<Expr> >::iterator, bool> res =
              branchTargets.insert(std::make_pair(
                  caseSuccessor, ConstantExpr::alloc(0, Expr::Bool)));

          res.first->second = OrExpr::create(match, res.first->second);

          // Only add basic blocks which have not been target of a branch yet
          if (res.second) {
            bbOrder.push_back(caseSuccessor);
          }
        }
      }

      // Check if control could take the default case
      bool res;
      bool success = solver->mayBeTrue(state, defaultValue, res);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      if (res) {
        std::pair<std::map<BasicBlock *, ref<Expr> >::iterator, bool> ret =
            branchTargets.insert(
                std::make_pair(si->getDefaultDest(), defaultValue));
        if (ret.second) {
          bbOrder.push_back(si->getDefaultDest());
        }
      }

      // Fork the current state with each state having one of the possible
      // successors of this switch
      std::vector< ref<Expr> > conditions;
      for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                                               ie = bbOrder.end();
           it != ie; ++it) {
        conditions.push_back(branchTargets[*it]);
      }
      std::vector<ExecutionState*> branches;
      branch(state, conditions, branches);

      std::vector<ExecutionState*>::iterator bit = branches.begin();
      for (std::vector<BasicBlock *>::iterator it = bbOrder.begin(),
                                               ie = bbOrder.end();
           it != ie; ++it) {
        ExecutionState *es = *bit;
        if (es)
          transferToBasicBlock(*it, bb, *es);
        ++bit;
      }
    }
    break;
 }
  case Instruction::Unreachable:
    // Note that this is not necessarily an internal bug, llvm will
    // generate unreachable instructions in cases where it knows the
    // program will crash. So it is effectively a SEGV or internal
    // error.
    terminateStateOnExecError(state, "reached \"unreachable\" instruction");
    break;

  case Instruction::Invoke:
  case Instruction::Call: {
    CallSite cs(i);

    unsigned numArgs = cs.arg_size();
    Value *fp = cs.getCalledValue();
    Function *f = getTargetFunction(fp, state);

    // Skip debug intrinsics, we can't evaluate their metadata arguments.
    if (f && isDebugIntrinsic(f, kmodule))
      break;

    if (isa<InlineAsm>(fp)) {
      terminateStateOnExecError(state, "inline assembly is unsupported");
      break;
    }
    // evaluate arguments
    std::vector< ref<Expr> > arguments;
    arguments.reserve(numArgs);

    for (unsigned j=0; j<numArgs; ++j)
      arguments.push_back(eval(ki, j+1, state).value);

    if (f) {
      const FunctionType *fType = 
        dyn_cast<FunctionType>(cast<PointerType>(f->getType())->getElementType());
      const FunctionType *fpType =
        dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());

      // special case the call with a bitcast case
      if (fType != fpType) {
        assert(fType && fpType && "unable to get function type");

        // XXX check result coercion

        // XXX this really needs thought and validation
        unsigned i=0;
        for (std::vector< ref<Expr> >::iterator
               ai = arguments.begin(), ie = arguments.end();
             ai != ie; ++ai) {
          Expr::Width to, from = (*ai)->getWidth();
            
          if (i<fType->getNumParams()) {
            to = getWidthForLLVMType(fType->getParamType(i));

            if (from != to) {
              // XXX need to check other param attrs ?
              bool isSExt = cs.paramHasAttr(i+1, llvm::Attribute::SExt);
              if (isSExt) {
                arguments[i] = SExtExpr::create(arguments[i], to);
              } else {
                arguments[i] = ZExtExpr::create(arguments[i], to);
              }
            }
          }
            
          i++;
        }
      }

      executeCall(state, ki, f, arguments);
    } else {
      ref<Expr> v = eval(ki, 0, state).value;

      ExecutionState *free = &state;
      bool hasInvalid = false, first = true;

      /* XXX This is wasteful, no need to do a full evaluate since we
         have already got a value. But in the end the caches should
         handle it for us, albeit with some overhead. */
      do {
        ref<ConstantExpr> value;
        bool success = solver->getValue(*free, v, value);
        assert(success && "FIXME: Unhandled solver failure");
        (void) success;
        StatePair res = fork(*free, EqExpr::create(v, value), true);
        if (res.first) {
          uint64_t addr = value->getZExtValue();
          if (legalFunctions.count(addr)) {
            f = (Function*) addr;

            // Don't give warning on unique resolution
            if (res.second || !first)
              klee_warning_once((void*) (unsigned long) addr, 
                                "resolved symbolic function pointer to: %s",
                                f->getName().data());

            executeCall(*res.first, ki, f, arguments);
          } else {
            if (!hasInvalid) {
              terminateStateOnExecError(state, "invalid function pointer");
              hasInvalid = true;
            }
          }
        }

        first = false;
        free = res.second;
      } while (free);
    }
    break;
  }
  case Instruction::PHI: {
    ref<Expr> result = eval(ki, state.incomingBBIndex, state).value;
    bindLocal(ki, state, result);
    break;
  }

    // Special instructions
  case Instruction::Select: {
    // NOTE: It is not required that operands 1 and 2 be of scalar type.
    ref<Expr> cond = eval(ki, 0, state).value;
    ref<Expr> tExpr = eval(ki, 1, state).value;
    ref<Expr> fExpr = eval(ki, 2, state).value;
    ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::VAArg:
    terminateStateOnExecError(state, "unexpected VAArg instruction");
    break;

    // Arithmetic / logical

  case Instruction::Add: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, AddExpr::create(left, right));
    break;
  }

  case Instruction::Sub: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, SubExpr::create(left, right));
    break;
  }
 
  case Instruction::Mul: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    bindLocal(ki, state, MulExpr::create(left, right));
    break;
  }

  case Instruction::UDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = UDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SDiv: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SDivExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::URem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = URemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::SRem: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = SRemExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::And: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AndExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Or: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = OrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Xor: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = XorExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::Shl: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = ShlExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::LShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = LShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::AShr: {
    ref<Expr> left = eval(ki, 0, state).value;
    ref<Expr> right = eval(ki, 1, state).value;
    ref<Expr> result = AShrExpr::create(left, right);
    bindLocal(ki, state, result);
    break;
  }

    // Compare

  case Instruction::ICmp: {
    CmpInst *ci = cast<CmpInst>(i);
    ICmpInst *ii = cast<ICmpInst>(ci);

    switch(ii->getPredicate()) {
    case ICmpInst::ICMP_EQ: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = EqExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_NE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = NeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_UGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgtExpr::create(left, right);
      bindLocal(ki, state,result);
      break;
    }

    case ICmpInst::ICMP_UGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_ULE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = UleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgtExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SGE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SgeExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLT: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SltExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    case ICmpInst::ICMP_SLE: {
      ref<Expr> left = eval(ki, 0, state).value;
      ref<Expr> right = eval(ki, 1, state).value;
      ref<Expr> result = SleExpr::create(left, right);
      bindLocal(ki, state, result);
      break;
    }

    default:
      terminateStateOnExecError(state, "invalid ICmp predicate");
    }
    break;
  }
 
    // Memory instructions...
  case Instruction::Alloca: {
    AllocaInst *ai = cast<AllocaInst>(i);
    unsigned elementSize = 
      kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
    ref<Expr> size = Expr::createPointer(elementSize);
    if (ai->isArrayAllocation()) {
      ref<Expr> count = eval(ki, 0, state).value;
      count = Expr::createZExtToPointerWidth(count);
      size = MulExpr::create(size, count);
    }
    executeAlloc(state, size, true, ki);
    break;
  }

  case Instruction::Load: {
    double T0;
    if (measureTime)
      T0= util::getWallTime();
    ref<Expr> base = eval(ki, 0, state).value;
    if (measureTime)
      mem_op_eval_time += util::getWallTime() - T0;
    executeMemoryOperation(state, false, base, 0, ki, "load 0, instCtr: " + std::to_string(instCtr));
    if (measureTime)
      run_mem_op_time += (util::getWallTime() - T0);
    break;
  }
  case Instruction::Store: {
    double T0;
    if (measureTime)
      T0 = util::getWallTime();
    ref<Expr> base = eval(ki, 1, state).value;
    ref<Expr> value = eval(ki, 0, state).value;
    if (measureTime) 
      mem_op_eval_time += util::getWallTime() - T0;
    executeMemoryOperation(state, true, base, value, 0, "store 0, instCtr: " + std::to_string(instCtr));
    if (measureTime)
      run_mem_op_time += (util::getWallTime() - T0);
    break;
  }

  case Instruction::GetElementPtr: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
    ref<Expr> base = eval(ki, 0, state).value;

    for (std::vector< std::pair<unsigned, uint64_t> >::iterator 
           it = kgepi->indices.begin(), ie = kgepi->indices.end(); 
         it != ie; ++it) {
      uint64_t elementSize = it->second;
      ref<Expr> index = eval(ki, it->first, state).value;
      base = AddExpr::create(base,
                             MulExpr::create(Expr::createSExtToPointerWidth(index),
                                             Expr::createPointer(elementSize)));
    }
    if (kgepi->offset)
      base = AddExpr::create(base,
                             Expr::createPointer(kgepi->offset));
    bindLocal(ki, state, base);
    break;
  }

    // Conversion
  case Instruction::Trunc: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ExtractExpr::create(eval(ki, 0, state).value,
                                           0,
                                           getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ZExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = ZExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }
  case Instruction::SExt: {
    CastInst *ci = cast<CastInst>(i);
    ref<Expr> result = SExtExpr::create(eval(ki, 0, state).value,
                                        getWidthForLLVMType(ci->getType()));
    bindLocal(ki, state, result);
    break;
  }

  case Instruction::IntToPtr: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width pType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    bindLocal(ki, state, ZExtExpr::create(arg, pType));
    break;
  }
  case Instruction::PtrToInt: {
    CastInst *ci = cast<CastInst>(i);
    Expr::Width iType = getWidthForLLVMType(ci->getType());
    ref<Expr> arg = eval(ki, 0, state).value;
    bindLocal(ki, state, ZExtExpr::create(arg, iType));
    break;
  }

  case Instruction::BitCast: {
    ref<Expr> result = eval(ki, 0, state).value;
    bindLocal(ki, state, result);
    break;
  }

    // Floating point instructions

  case Instruction::FAdd: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FAdd operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.add(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FSub: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FSub operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.subtract(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FMul: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FMul operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.multiply(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FDiv: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FDiv operation");

    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.divide(APFloat(*fpWidthToSemantics(right->getWidth()), right->getAPValue()), APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FRem: {
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FRem operation");
    llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()), left->getAPValue());
    Res.mod(APFloat(*fpWidthToSemantics(right->getWidth()),right->getAPValue()),
            APFloat::rmNearestTiesToEven);
    bindLocal(ki, state, ConstantExpr::alloc(Res.bitcastToAPInt()));
    break;
  }

  case Instruction::FPTrunc: {
    FPTruncInst *fi = cast<FPTruncInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > arg->getWidth())
      return terminateStateOnExecError(state, "Unsupported FPTrunc operation");

    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType),
                llvm::APFloat::rmNearestTiesToEven,
                &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPExt: {
    FPExtInst *fi = cast<FPExtInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || arg->getWidth() > resultType)
      return terminateStateOnExecError(state, "Unsupported FPExt operation");
    llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    bool losesInfo = false;
    Res.convert(*fpWidthToSemantics(resultType),
                llvm::APFloat::rmNearestTiesToEven,
                &losesInfo);
    bindLocal(ki, state, ConstantExpr::alloc(Res));
    break;
  }

  case Instruction::FPToUI: {
    FPToUIInst *fi = cast<FPToUIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToUI operation");

    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());
    uint64_t value = 0;
    bool isExact = true;
    Arg.convertToInteger(&value, resultType, false,
                         llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::FPToSI: {
    FPToSIInst *fi = cast<FPToSIInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
      return terminateStateOnExecError(state, "Unsupported FPToSI operation");
    llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()), arg->getAPValue());

    uint64_t value = 0;
    bool isExact = true;
    Arg.convertToInteger(&value, resultType, true,
                         llvm::APFloat::rmTowardZero, &isExact);
    bindLocal(ki, state, ConstantExpr::alloc(value, resultType));
    break;
  }

  case Instruction::UIToFP: {
    UIToFPInst *fi = cast<UIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported UIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), false,
                       llvm::APFloat::rmNearestTiesToEven);

    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::SIToFP: {
    SIToFPInst *fi = cast<SIToFPInst>(i);
    Expr::Width resultType = getWidthForLLVMType(fi->getType());
    ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, state).value,
                                       "floating point");
    const llvm::fltSemantics *semantics = fpWidthToSemantics(resultType);
    if (!semantics)
      return terminateStateOnExecError(state, "Unsupported SIToFP operation");
    llvm::APFloat f(*semantics, 0);
    f.convertFromAPInt(arg->getAPValue(), true,
                       llvm::APFloat::rmNearestTiesToEven);

    bindLocal(ki, state, ConstantExpr::alloc(f));
    break;
  }

  case Instruction::FCmp: {
    FCmpInst *fi = cast<FCmpInst>(i);
    ref<ConstantExpr> left = toConstant(state, eval(ki, 0, state).value,
                                        "floating point");
    ref<ConstantExpr> right = toConstant(state, eval(ki, 1, state).value,
                                         "floating point");
    if (!fpWidthToSemantics(left->getWidth()) ||
        !fpWidthToSemantics(right->getWidth()))
      return terminateStateOnExecError(state, "Unsupported FCmp operation");

    APFloat LHS(*fpWidthToSemantics(left->getWidth()),left->getAPValue());
    APFloat RHS(*fpWidthToSemantics(right->getWidth()),right->getAPValue());
    APFloat::cmpResult CmpRes = LHS.compare(RHS);

    bool Result = false;
    switch( fi->getPredicate() ) {
      // Predicates which only care about whether or not the operands are NaNs.
    case FCmpInst::FCMP_ORD:
      Result = CmpRes != APFloat::cmpUnordered;
      break;

    case FCmpInst::FCMP_UNO:
      Result = CmpRes == APFloat::cmpUnordered;
      break;

      // Ordered comparisons return false if either operand is NaN.  Unordered
      // comparisons return true if either operand is NaN.
    case FCmpInst::FCMP_UEQ:
      if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
      }
      [[fallthrough]];
    case FCmpInst::FCMP_OEQ:
      Result = CmpRes == APFloat::cmpEqual;
      break;

    case FCmpInst::FCMP_UGT:
      if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
      }
      [[fallthrough]];
    case FCmpInst::FCMP_OGT:
      Result = CmpRes == APFloat::cmpGreaterThan;
      break;

    case FCmpInst::FCMP_UGE:
      if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
      }
      [[fallthrough]];      
    case FCmpInst::FCMP_OGE:
      Result = CmpRes == APFloat::cmpGreaterThan || CmpRes == APFloat::cmpEqual;
      break;

    case FCmpInst::FCMP_ULT:
      if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
      }
      [[fallthrough]];      
    case FCmpInst::FCMP_OLT:
      Result = CmpRes == APFloat::cmpLessThan;
      break;

    case FCmpInst::FCMP_ULE:
      if (CmpRes == APFloat::cmpUnordered) {
        Result = true;
        break;
      }
      [[fallthrough]];      
    case FCmpInst::FCMP_OLE:
      Result = CmpRes == APFloat::cmpLessThan || CmpRes == APFloat::cmpEqual;
      break;

    case FCmpInst::FCMP_UNE:
      Result = CmpRes == APFloat::cmpUnordered || CmpRes != APFloat::cmpEqual;
      break;
    case FCmpInst::FCMP_ONE:
      Result = CmpRes != APFloat::cmpUnordered && CmpRes != APFloat::cmpEqual;
      break;

    default:
      assert(0 && "Invalid FCMP predicate!");
    case FCmpInst::FCMP_FALSE:
      Result = false;
      break;
    case FCmpInst::FCMP_TRUE:
      Result = true;
      break;
    }

    bindLocal(ki, state, ConstantExpr::alloc(Result, Expr::Bool));
    break;
  }
  case Instruction::InsertValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;
    ref<Expr> val = eval(ki, 1, state).value;

    ref<Expr> l = NULL, r = NULL;
    unsigned lOffset = kgepi->offset*8, rOffset = kgepi->offset*8 + val->getWidth();

    if (lOffset > 0)
      l = ExtractExpr::create(agg, 0, lOffset);
    if (rOffset < agg->getWidth())
      r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);

    ref<Expr> result;
    if (!l.isNull() && !r.isNull())
      result = ConcatExpr::create(r, ConcatExpr::create(val, l));
    else if (!l.isNull())
      result = ConcatExpr::create(val, l);
    else if (!r.isNull())
      result = ConcatExpr::create(r, val);
    else
      result = val;

    bindLocal(ki, state, result);
    break;
  }
  case Instruction::ExtractValue: {
    KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

    ref<Expr> agg = eval(ki, 0, state).value;

    ref<Expr> result = ExtractExpr::create(agg, kgepi->offset*8, getWidthForLLVMType(i->getType()));

    bindLocal(ki, state, result);
    break;
  }
  case Instruction::Fence: {
    // Ignore for now
    break;
  }
  case Instruction::InsertElement: {
    InsertElementInst *iei = cast<InsertElementInst>(i);
    ref<Expr> vec = eval(ki, 0, state).value;
    ref<Expr> newElt = eval(ki, 1, state).value;
    ref<Expr> idx = eval(ki, 2, state).value;
    
    ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
    if (cIdx == NULL) {
      terminateStateOnError(
          state, "InsertElement, support for symbolic index not implemented",
          Unhandled);
      return;
    }
    uint64_t iIdx = cIdx->getZExtValue();
    const llvm::VectorType *vt = iei->getType();
    unsigned EltBits = getWidthForLLVMType(vt->getElementType());

    //printf("\n Calling InsertElement at idx %lu \n", iIdx);

    if (iIdx >= vt->getNumElements()) {
      // Out of bounds write
      terminateStateOnError(state, "Out of bounds write when inserting element",
                            BadVectorAccess);
      return;
    }

    const unsigned elementCount = vt->getNumElements();
    llvm::SmallVector<ref<Expr>, 8> elems;
    elems.reserve(elementCount);
    for (unsigned i = 0; i < elementCount; ++i) {
      // evalConstant() will use ConcatExpr to build vectors with the
      // zero-th element leftmost (most significant bits), followed
      // by the next element (second leftmost) and so on. This means
      // that we have to adjust the index so we read left to right
      // rather than right to left.
      unsigned bitOffset = EltBits * (elementCount - i - 1);
      //printf("bitOffset is %u \n\n",bitOffset);
      if (i == iIdx) {
	//printf("Found insert index at %u \n\n", bitOffset);
      }
      elems.push_back(i == iIdx ? newElt
                                : ExtractExpr::create(vec, bitOffset, EltBits));
    }

    ref<Expr> Result = ConcatExpr::createN(elementCount, elems.data());
    bindLocal(ki, state, Result);
    break;
  }
  case Instruction::ExtractElement: {
    ExtractElementInst *eei = cast<ExtractElementInst>(i);
    ref<Expr> vec = eval(ki, 0, state).value;
    ref<Expr> idx = eval(ki, 1, state).value;

    ConstantExpr *cIdx = dyn_cast<ConstantExpr>(idx);
    if (cIdx == NULL) {
      terminateStateOnError(
          state, "ExtractElement, support for symbolic index not implemented",
          Unhandled);
      return;
    }
    uint64_t iIdx = cIdx->getZExtValue();
    const llvm::VectorType *vt = eei->getVectorOperandType();
    unsigned EltBits = getWidthForLLVMType(vt->getElementType());

    if (iIdx >= vt->getNumElements()) {
      // Out of bounds read
      terminateStateOnError(state, "Out of bounds read when extracting element",
                            BadVectorAccess);
      return;
    }

    // evalConstant() will use ConcatExpr to build vectors with the
    // zero-th element left most (most significant bits), followed
    // by the next element (second left most) and so on. This means
    // that we have to adjust the index so we read left to right
    // rather than right to left.
    unsigned bitOffset = EltBits*(vt->getNumElements() - iIdx -1);
    ref<Expr> Result = ExtractExpr::create(vec, bitOffset, EltBits);
    bindLocal(ki, state, Result);
    break;
  }
  case Instruction::ShuffleVector:
    // Should never happen due to Scalarizer pass removing ShuffleVector
    // instructions.
    terminateStateOnExecError(state, "Unexpected ShuffleVector instruction");
    break;
  // Other instructions...
  // Unhandled
  default:
    terminateStateOnExecError(state, "illegal instruction");
    break;
  }
}

void Executor::updateStates(ExecutionState *current) {
  if (searcher) {
    searcher->update(current, addedStates, removedStates);
    searcher->update(nullptr, continuedStates, pausedStates);
    pausedStates.clear();
    continuedStates.clear();
  }
  
  states.insert(addedStates.begin(), addedStates.end());
  addedStates.clear();

  for (std::vector<ExecutionState *>::iterator it = removedStates.begin(),
                                               ie = removedStates.end();
       it != ie; ++it) {
    ExecutionState *es = *it;
    std::set<ExecutionState*>::iterator it2 = states.find(es);
    assert(it2!=states.end());
    states.erase(it2);
    std::map<ExecutionState*, std::vector<SeedInfo> >::iterator it3 = 
      seedMap.find(es);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    processTree->remove(es->ptreeNode);
    delete es;
  }
  removedStates.clear();
}

template <typename TypeIt>
void Executor::computeOffsets(KGEPInstruction *kgepi, TypeIt ib, TypeIt ie) {
  ref<ConstantExpr> constantOffset =
    ConstantExpr::alloc(0, Context::get().getPointerWidth());
  uint64_t index = 1;
  for (TypeIt ii = ib; ii != ie; ++ii) {
    if (StructType *st = dyn_cast<StructType>(*ii)) {
      const StructLayout *sl = kmodule->targetData->getStructLayout(st);
      const ConstantInt *ci = cast<ConstantInt>(ii.getOperand());
      uint64_t addend = sl->getElementOffset((unsigned) ci->getZExtValue());
      constantOffset = constantOffset->Add(ConstantExpr::alloc(addend,
                                                               Context::get().getPointerWidth()));
    } else {
      const SequentialType *set = cast<SequentialType>(*ii);
      uint64_t elementSize = 
        kmodule->targetData->getTypeStoreSize(set->getElementType());
      Value *operand = ii.getOperand();
      if (Constant *c = dyn_cast<Constant>(operand)) {
        ref<ConstantExpr> index = 
          evalConstant(c)->SExt(Context::get().getPointerWidth());
        ref<ConstantExpr> addend = 
          index->Mul(ConstantExpr::alloc(elementSize,
                                         Context::get().getPointerWidth()));
        constantOffset = constantOffset->Add(addend);
      } else {
        kgepi->indices.push_back(std::make_pair(index, elementSize));
      }
    }
    index++;
  }
  kgepi->offset = constantOffset->getZExtValue();
}

void Executor::bindInstructionConstants(KInstruction *KI) {
  KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(KI);

  if (GetElementPtrInst *gepi = dyn_cast<GetElementPtrInst>(KI->inst)) {
    computeOffsets(kgepi, gep_type_begin(gepi), gep_type_end(gepi));
  } else if (InsertValueInst *ivi = dyn_cast<InsertValueInst>(KI->inst)) {
    computeOffsets(kgepi, iv_type_begin(ivi), iv_type_end(ivi));
    assert(kgepi->indices.empty() && "InsertValue constant offset expected");
  } else if (ExtractValueInst *evi = dyn_cast<ExtractValueInst>(KI->inst)) {
    computeOffsets(kgepi, ev_type_begin(evi), ev_type_end(evi));
    assert(kgepi->indices.empty() && "ExtractValue constant offset expected");
  }
}

void Executor::bindModuleConstants() {
  for (std::vector<KFunction*>::iterator it = kmodule->functions.begin(), 
         ie = kmodule->functions.end(); it != ie; ++it) {
    KFunction *kf = *it;
    for (unsigned i=0; i<kf->numInstructions; ++i)
      bindInstructionConstants(kf->instructions[i]);
  }
  
  kmodule->constantTable = new Cell[kmodule->constants.size()];
  for (unsigned i=0; i<kmodule->constants.size(); ++i) {    
    Cell &c = kmodule->constantTable[i];
    // assert(c);
    assert(kmodule->constants[i]);
    c.value = evalConstant(kmodule->constants[i]);
  }
}

void Executor::checkMemoryUsage() {
  if (!MaxMemory)
    return;
  if ((stats::instructions & 0xFFFF) == 0) {
    // We need to avoid calling GetTotalMallocUsage() often because it
    // is O(elts on freelist). This is really bad since we start
    // to pummel the freelist once we hit the memory cap.
    unsigned mbs = (util::GetTotalMallocUsage() >> 20) +
                   (memory->getUsedDeterministicSize() >> 20);

    if (mbs > MaxMemory) {
      if (mbs > MaxMemory + 100) {
        // just guess at how many to kill
        unsigned numStates = states.size();
        unsigned toKill = std::max(1U, numStates - numStates * MaxMemory / mbs);
        klee_warning("killing %d states (over memory cap)", toKill);
        std::vector<ExecutionState *> arr(states.begin(), states.end());
        for (unsigned i = 0, N = arr.size(); N && i < toKill; ++i, --N) {
          unsigned idx = rand() % N;
          // Make two pulls to try and not hit a state that
          // covered new code.
          if (arr[idx]->coveredNew)
            idx = rand() % N;

          std::swap(arr[idx], arr[N - 1]);
          terminateStateEarly(*arr[N - 1], "Memory limit exceeded.");
        }
      }
      atMemoryLimit = true;
    } else {
      atMemoryLimit = false;
    }
  }
}

void Executor::doDumpStates() {
  if (!DumpStatesOnHalt || states.empty())
    return;
  klee_message("halting execution, dumping remaining states");
  for (std::set<ExecutionState *>::iterator it = states.begin(),
                                            ie = states.end();
       it != ie; ++it) {
    ExecutionState &state = **it;
    stepInstruction(state); // keep stats rolling
    terminateStateEarly(state, "Execution halting.");
  }
  updateStates(0);
}

//Slightly modified for TASE because we don't use the
//KLEE state tracking structures.
void Executor::run(ExecutionState  & initialState) {
  if (usingSeeds) {
    LOG_TASE("ERROR: Seeds not supported in TASE \n");LOG_FLUSH();
    std::exit(EXIT_FAILURE);
  }
  haltExecution = false;
  int instCtr = 0; 
  while ( !haltExecution) { 
    double instStartTime = util::getWallTime();
    KInstruction *ki = GlobalExecutionStatePtr->pc;
    stepInstruction(*GlobalExecutionStatePtr);
    executeInstruction(*GlobalExecutionStatePtr, ki);
    //LOG_TASE("Spent %lf seconds on inst %d in core interpreter \n", util::getWallTime() -instStartTime, instCtr);LOG_FLUSH();
    instCtr++;
  } 
  
}

std::string Executor::getAddressInfo(ExecutionState &state, 
                                     ref<Expr> address) const{
  std::string Str;
  llvm::raw_string_ostream info(Str);
  info << "\taddress: " << address << "\n";
  uint64_t example;
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(address)) {
    example = CE->getZExtValue();
  } else {
    ref<ConstantExpr> value;
    bool success = solver->getValue(state, address, value);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    example = value->getZExtValue();
    info << "\texample: " << example << "\n";
    std::pair< ref<Expr>, ref<Expr> > res = solver->getRange(state, address);
    info << "\trange: [" << res.first << ", " << res.second <<"]\n";
  }
  
  MemoryObject hack((unsigned) example);    
  MemoryMap::iterator lower = state.addressSpace.objects.upper_bound(&hack);
  info << "\tnext: ";
  if (lower==state.addressSpace.objects.end()) {
    info << "none\n";
  } else {
    const MemoryObject *mo = lower->first;
    std::string alloc_info;
    mo->getAllocInfo(alloc_info);
    info << "object at " << mo->address
         << " of size " << mo->size << "\n"
         << "\t\t" << alloc_info << "\n";
  }
  if (lower!=state.addressSpace.objects.begin()) {
    --lower;
    info << "\tprev: ";
    if (lower==state.addressSpace.objects.end()) {
      info << "none\n";
    } else {
      const MemoryObject *mo = lower->first;
      std::string alloc_info;
      mo->getAllocInfo(alloc_info);
      info << "object at " << mo->address 
           << " of size " << mo->size << "\n"
           << "\t\t" << alloc_info << "\n";
    }
  }

  return info.str();
}

void Executor::pauseState(ExecutionState &state){
  auto it = std::find(continuedStates.begin(), continuedStates.end(), &state);
  // If the state was to be continued, but now gets paused again
  if (it != continuedStates.end()){
    // ...just don't continue it
    std::swap(*it, continuedStates.back());
    continuedStates.pop_back();
  } else {
    pausedStates.push_back(&state);
  }
}

void Executor::continueState(ExecutionState &state){
  auto it = std::find(pausedStates.begin(), pausedStates.end(), &state);
  // If the state was to be paused, but now gets continued again
  if (it != pausedStates.end()){
    // ...don't pause it
    std::swap(*it, pausedStates.back());
    pausedStates.pop_back();
  } else {
    continuedStates.push_back(&state);
  }
}

void Executor::terminateState(ExecutionState &state) {
  if (replayKTest && replayPosition!=replayKTest->numObjects) {
    klee_warning_once(replayKTest,
                      "replay did not consume all objects in test input.");
  }

  interpreterHandler->incPathsExplored();

  std::vector<ExecutionState *>::iterator it =
      std::find(addedStates.begin(), addedStates.end(), &state);
  if (it==addedStates.end()) {
    state.pc = state.prevPC;

    removedStates.push_back(&state);
  } else {
    // never reached searcher, just delete immediately
    std::map< ExecutionState*, std::vector<SeedInfo> >::iterator it3 = 
      seedMap.find(&state);
    if (it3 != seedMap.end())
      seedMap.erase(it3);
    addedStates.erase(it);
    processTree->remove(state.ptreeNode);
    printf(" WOULD NORMAL DELETE STATE HERE \n \n \n \n ");
    delete &state;
  }
}

void Executor::terminateStateEarly(ExecutionState &state, 
                                   const Twine &message) {
  if (!OnlyOutputStatesCoveringNew || state.coveredNew ||
      (AlwaysOutputSeeds && seedMap.count(&state)))
    interpreterHandler->processTestCase(state, (message + "\n").str().c_str(),
                                        "early");
  terminateState(state);
}

void Executor::terminateStateOnExit(ExecutionState &state) {
  if (!OnlyOutputStatesCoveringNew || state.coveredNew || 
      (AlwaysOutputSeeds && seedMap.count(&state)))
    interpreterHandler->processTestCase(state, 0, 0);
  terminateState(state);
}

const InstructionInfo & Executor::getLastNonKleeInternalInstruction(const ExecutionState &state,
    Instruction ** lastInstruction) {
  // unroll the stack of the applications state and find
  // the last instruction which is not inside a KLEE internal function
  ExecutionState::stack_ty::const_reverse_iterator it = state.stack.rbegin(),
      itE = state.stack.rend();

  // don't check beyond the outermost function (i.e. main())
  itE--;

  const InstructionInfo * ii = 0;
  if (kmodule->internalFunctions.count(it->kf->function) == 0){
    ii =  state.prevPC->info;
    *lastInstruction = state.prevPC->inst;
    //  Cannot return yet because even though
    //  it->function is not an internal function it might of
    //  been called from an internal function.
  }

  // Wind up the stack and check if we are in a KLEE internal function.
  // We visit the entire stack because we want to return a CallInstruction
  // that was not reached via any KLEE internal functions.
  for (;it != itE; ++it) {
    // check calling instruction and if it is contained in a KLEE internal function
    const Function * f = (*it->caller).inst->getParent()->getParent();
    if (kmodule->internalFunctions.count(f)){
      ii = 0;
      continue;
    }
    if (!ii){
      ii = (*it->caller).info;
      *lastInstruction = (*it->caller).inst;
    }
  }

  if (!ii) {
    // something went wrong, play safe and return the current instruction info
    *lastInstruction = state.prevPC->inst;
    return *state.prevPC->info;
  }
  return *ii;
}

bool Executor::shouldExitOn(enum TerminateReason termReason) {
  std::vector<TerminateReason>::iterator s = ExitOnErrorType.begin();
  std::vector<TerminateReason>::iterator e = ExitOnErrorType.end();

  for (; s != e; ++s)
    if (termReason == *s)
      return true;

  return false;
}

void Executor::terminateStateOnError(ExecutionState &state,
                                     const llvm::Twine &messaget,
                                     enum TerminateReason termReason,
                                     const char *suffix,
                                     const llvm::Twine &info) {
  std::string message = messaget.str();
  static std::set< std::pair<Instruction*, std::string> > emittedErrors;
  Instruction * lastInst;
  const InstructionInfo &ii = getLastNonKleeInternalInstruction(state, &lastInst);
  
  if (EmitAllErrors ||
      emittedErrors.insert(std::make_pair(lastInst, message)).second) {
    if (ii.file != "") {
      klee_message("ERROR: %s:%d: %s", ii.file.c_str(), ii.line, message.c_str());
    } else {
      klee_message("ERROR: (location information missing) %s", message.c_str());
    }
    if (!EmitAllErrors)
      klee_message("NOTE: now ignoring this error at this location");

    std::string MsgString;
    llvm::raw_string_ostream msg(MsgString);
    msg << "Error: " << message << "\n";
    if (ii.file != "") {
      msg << "File: " << ii.file << "\n";
      msg << "Line: " << ii.line << "\n";
      msg << "assembly.ll line: " << ii.assemblyLine << "\n";
    }
    msg << "Stack: \n";
    state.dumpStack(msg);

    std::string info_str = info.str();
    if (info_str != "")
      msg << "Info: \n" << info_str;

    std::string suffix_buf;
    if (!suffix) {
      suffix_buf = TerminateReasonNames[termReason];
      suffix_buf += ".err";
      suffix = suffix_buf.c_str();
    }

    interpreterHandler->processTestCase(state, msg.str().c_str(), suffix);
  }
    
  terminateState(state);

  if (shouldExitOn(termReason))
    haltExecution = true;
}

// XXX shoot me
static const char *okExternalsList[] = { "printf", 
                                         "fprintf", 
                                         "puts",
                                         "getpid" };
static std::set<std::string> okExternals(okExternalsList,
                                         okExternalsList + 
                                         (sizeof(okExternalsList)/sizeof(okExternalsList[0])));

void Executor::callExternalFunction(ExecutionState &state,
                                    KInstruction *target,
                                    Function *function,
                                    std::vector< ref<Expr> > &arguments) {
  // check if specialFunctionHandler wants it
  if (specialFunctionHandler->handle(state, function, target, arguments))
    return;
  
  if (NoExternals && !okExternals.count(function->getName())) {
    klee_warning("Disallowed call to external function: %s\n",
               function->getName().str().c_str());
    terminateStateOnError(state, "externals disallowed", User);
    return;
  }

  // normal external function handling path
  // allocate 128 bits for each argument (+return value) to support fp80's;
  // we could iterate through all the arguments first and determine the exact
  // size we need, but this is faster, and the memory usage isn't significant.
  uint64_t *args = (uint64_t*) alloca(2*sizeof(*args) * (arguments.size() + 1));
  memset(args, 0, 2 * sizeof(*args) * (arguments.size() + 1));
  unsigned wordIndex = 2;
  for (std::vector<ref<Expr> >::iterator ai = arguments.begin(), 
       ae = arguments.end(); ai!=ae; ++ai) {
    if (AllowExternalSymCalls) { // don't bother checking uniqueness
      ref<ConstantExpr> ce;
      bool success = solver->getValue(state, *ai, ce);
      assert(success && "FIXME: Unhandled solver failure");
      (void) success;
      ce->toMemory(&args[wordIndex]);
      wordIndex += (ce->getWidth()+63)/64;
    } else {
      ref<Expr> arg = toUnique(state, *ai);
      if (ConstantExpr *ce = dyn_cast<ConstantExpr>(arg)) {
        // XXX kick toMemory functions from here
        ce->toMemory(&args[wordIndex]);
        wordIndex += (ce->getWidth()+63)/64;
      } else {
        terminateStateOnExecError(state, 
                                  "external call with symbolic argument: " + 
                                  function->getName());
        return;
      }
    }
  }

  state.addressSpace.copyOutConcretes();

  if (!SuppressExternalWarnings) {

    std::string TmpStr;
    llvm::raw_string_ostream os(TmpStr);
    os << "calling external: " << function->getName().str() << "(";
    for (unsigned i=0; i<arguments.size(); i++) {
      os << arguments[i];
      if (i != arguments.size()-1)
	os << ", ";
    }
    os << ") at ";
    state.pc->printFileLine(os);
    
    if (AllExternalWarnings)
      klee_warning("%s", os.str().c_str());
    else
      klee_warning_once(function, "%s", os.str().c_str());
  }
  bool success = externalDispatcher->executeCall(function, target->inst, args);
  if (!success) {
    terminateStateOnError(state, "failed external call: " + function->getName(),
                          External);
    return;
  }

  if (!state.addressSpace.copyInConcretes()) {
    terminateStateOnError(state, "external modified read-only object",
                          External);
    return;
  }

  Type *resultType = target->inst->getType();
  if (resultType != Type::getVoidTy(function->getContext())) {
    ref<Expr> e = ConstantExpr::fromMemory((void*) args, 
                                           getWidthForLLVMType(resultType));
    bindLocal(target, state, e);
  }
}

ref<Expr> Executor::replaceReadWithSymbolic(ExecutionState &state, 
                                            ref<Expr> e) {
  unsigned n = interpreterOpts.MakeConcreteSymbolic;
  if (!n || replayKTest || replayPath)
    return e;

  // right now, we don't replace symbolics (is there any reason to?)
  if (!isa<ConstantExpr>(e))
    return e;

  if (n != 1 && random() % n)
    return e;

  // create a new fresh location, assert it is equal to concrete value in e
  // and return it.
  
  static unsigned id;
  const Array *array =
      arrayCache.CreateArray("rrws_arr" + llvm::utostr(++id),
                             Expr::getMinBytesForWidth(e->getWidth()));
  ref<Expr> res = Expr::createTempRead(array, e->getWidth());
  ref<Expr> eq = NotOptimizedExpr::create(EqExpr::create(e, res));
  llvm::errs() << "Making symbolic: " << eq << "\n";
  state.addConstraint(eq);
  return res;
}

ObjectState *Executor::bindObjectInState(ExecutionState &state, 
                                         const MemoryObject *mo,
                                         bool isLocal,
                                         const Array *array,
					 bool forTASE ) {
  ObjectState *os = array ? new ObjectState(mo, array,forTASE) : new ObjectState(mo, forTASE);
  state.addressSpace.bindObject(mo, os);

  
  
  // Its possible that multiple bindings of the same mo in the state
  // will put multiple copies on this list, but it doesn't really
  // matter because all we use this list for is to unbind the object
  // on function return.
  if (isLocal)
    state.stack.back().allocas.push_back(mo);

  return os;
}

void Executor::executeAlloc(ExecutionState &state,
                            ref<Expr> size,
                            bool isLocal,
                            KInstruction *target,
                            bool zeroMemory,
                            const ObjectState *reallocFrom) {
  size = toUnique(state, size);
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(size)) {
    const llvm::Value *allocSite = state.prevPC->inst;
    size_t allocationAlignment = getAllocationAlignment(allocSite);
    MemoryObject *mo =
        memory->allocate(CE->getZExtValue(), isLocal, /*isGlobal=*/false,
                         allocSite, allocationAlignment);
    if (!mo) {
      bindLocal(target, state, 
                ConstantExpr::alloc(0, Context::get().getPointerWidth()));
    } else {
      ObjectState *os = bindObjectInState(state, mo, isLocal);
      if (zeroMemory) {
        os->initializeToZero();
      } else {
        os->initializeToRandom();
      }
      bindLocal(target, state, mo->getBaseExpr());
      
      if (reallocFrom) {
        unsigned count = std::min(reallocFrom->size, os->size);
        for (unsigned i=0; i<count; i++)
          os->write(i, reallocFrom->read8(i));
        state.addressSpace.unbindObject(reallocFrom->getObject());
      }
    }
  } else {
    // XXX For now we just pick a size. Ideally we would support
    // symbolic sizes fully but even if we don't it would be better to
    // "smartly" pick a value, for example we could fork and pick the
    // min and max values and perhaps some intermediate (reasonable
    // value).
    // 
    // It would also be nice to recognize the case when size has
    // exactly two values and just fork (but we need to get rid of
    // return argument first). This shows up in pcre when llvm
    // collapses the size expression with a select.

    ref<ConstantExpr> example;
    bool success = solver->getValue(state, size, example);
    assert(success && "FIXME: Unhandled solver failure");
    (void) success;
    
    // Try and start with a small example.
    Expr::Width W = example->getWidth();
    while (example->Ugt(ConstantExpr::alloc(128, W))->isTrue()) {
      ref<ConstantExpr> tmp = example->LShr(ConstantExpr::alloc(1, W));
      bool res;
      bool success = solver->mayBeTrue(state, EqExpr::create(tmp, size), res);
      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;
      if (!res)
        break;
      example = tmp;
    }

    StatePair fixedSize = fork(state, EqExpr::create(example, size), true);
    
    if (fixedSize.second) { 
      // Check for exactly two values
      ref<ConstantExpr> tmp;
      bool success = solver->getValue(*fixedSize.second, size, tmp);
      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;
      bool res;
      success = solver->mustBeTrue(*fixedSize.second, 
                                   EqExpr::create(tmp, size),
                                   res);
      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;
      if (res) {
        executeAlloc(*fixedSize.second, tmp, isLocal,
                     target, zeroMemory, reallocFrom);
      } else {
        // See if a *really* big value is possible. If so assume
        // malloc will fail for it, so lets fork and return 0.
        StatePair hugeSize = 
          fork(*fixedSize.second, 
               UltExpr::create(ConstantExpr::alloc(1U<<31, W), size),
               true);
        if (hugeSize.first) {
          klee_message("NOTE: found huge malloc, returning 0");
          bindLocal(target, *hugeSize.first, 
                    ConstantExpr::alloc(0, Context::get().getPointerWidth()));
        }
        
        if (hugeSize.second) {

          std::string Str;
          llvm::raw_string_ostream info(Str);
          ExprPPrinter::printOne(info, "  size expr", size);
          info << "  concretization : " << example << "\n";
          info << "  unbound example: " << tmp << "\n";
          terminateStateOnError(*hugeSize.second, "concretized symbolic size",
                                Model, NULL, info.str());
        }
      }
    }

    if (fixedSize.first) // can be zero when fork fails
      executeAlloc(*fixedSize.first, example, isLocal, 
                   target, zeroMemory, reallocFrom);
  }
}

void Executor::executeFree(ExecutionState &state,
                           ref<Expr> address,
                           KInstruction *target) {
  StatePair zeroPointer = fork(state, Expr::createIsZero(address), true);
  if (zeroPointer.first) {
    if (target)
      bindLocal(target, *zeroPointer.first, Expr::createPointer(0));
  }
  if (zeroPointer.second) { // address != 0
    ExactResolutionList rl;
    resolveExact(*zeroPointer.second, address, rl, "free");
    
    for (Executor::ExactResolutionList::iterator it = rl.begin(), 
           ie = rl.end(); it != ie; ++it) {
      const MemoryObject *mo = it->first.first;
      if (mo->isLocal) {
        terminateStateOnError(*it->second, "free of alloca", Free, NULL,
                              getAddressInfo(*it->second, address));
      } else if (mo->isGlobal) {
        terminateStateOnError(*it->second, "free of global", Free, NULL,
                              getAddressInfo(*it->second, address));
      } else {
        it->second->addressSpace.unbindObject(mo);
        if (target)
          bindLocal(target, *it->second, Expr::createPointer(0));
      }
    }
  }
}

void Executor::resolveExact(ExecutionState &state,
                            ref<Expr> p,
                            ExactResolutionList &results, 
                            const std::string &name) {
  // XXX we may want to be capping this?
  ResolutionList rl;
  state.addressSpace.resolve(state, solver, p, rl);
  
  ExecutionState *unbound = &state;
  for (ResolutionList::iterator it = rl.begin(), ie = rl.end(); 
       it != ie; ++it) {
    ref<Expr> inBounds = EqExpr::create(p, it->first->getBaseExpr());
    
    StatePair branches = fork(*unbound, inBounds, true);
    
    if (branches.first)
      results.push_back(std::make_pair(*it, branches.first));

    unbound = branches.second;
    if (!unbound) // Fork failure
      break;
  }

  if (unbound) {
    terminateStateOnError(*unbound, "memory error: invalid pointer: " + name,
                          Ptr, NULL, getAddressInfo(*unbound, p));
  }
}

void Executor::executeMemoryOperation(ExecutionState &state,
                                      bool isWrite,
                                      ref<Expr> address,
                                      ref<Expr> value /* undef if read */,
                                      KInstruction *target /* undef if write */,
                                      const std::string& reason) {

  Expr::Width type = (isWrite ? value->getWidth() : 
                      getWidthForLLVMType(target->inst->getType()));
  unsigned bytes = Expr::getMinBytesForWidth(type);
  
  if (SimplifySymIndices) {
    if (!isa<ConstantExpr>(address))
      address = state.constraints.simplifyExpr(address);
    if (isWrite && !isa<ConstantExpr>(value))
      value = state.constraints.simplifyExpr(value);
  }

  ObjectPair op;
  bool success;
  
//Fast path for TASE where offset is concrete
  ConstantExpr * CE = dyn_cast<ConstantExpr> (address);
  if (CE) {
    success = state.addressSpace.resolveOne(CE, op);
  } else {
    
    // fast path: single in-bounds resolution
    double T4 = util::getWallTime();
    solver->setTimeout(coreSolverTimeout);
    ExecutionState dummy = ExecutionState(getDepCons(address,false));
    //if (!state.addressSpace.resolveOne(state, solver, address, op, success)) {
    if (!state.addressSpace.resolveOne(dummy, solver, address, op, success)) {
      std::cout << "resolveOne failure! " << std::endl;
      fflush(stdout);
      //address = toConstant(state, address, "resolveOne failure");
      address = toConstant(dummy, address, "resolveOne failure");
      success = state.addressSpace.resolveOne(cast<ConstantExpr>(address), op);
    }
    solver->setTimeout(0);
    //LOG_TASE("%lf seconds in T4 \n", util::getWallTime() - T4);LOG_FLUSH();
  }
  
  if (!success) {
    std::string ss;
    llvm::raw_string_ostream tmp(ss);
    address->print(tmp);
    LOG_TASE("Could not resolve address to MO: %llx, RIP: %lx\nReason: %s\naddress was %s\n", std::stoull(tmp.str().c_str(), nullptr, 0), target_ctx_gregs[GREG_RIP].u64, reason.c_str(), CE ? "" : "not ")
    worker_error(Stopped, Running);
    
  } else {
    const MemoryObject *mo = op.first;

    //------------------New fast path:
    //Cherry-pick in-bounds reads at constant offsets.

    if (optimizeConstMemOps && CE->getZExtValue() + bytes <= mo->address + mo->size) {
      unsigned offset = CE->getZExtValue() - mo->address;
      const ObjectState *os = op.second;
      
      if (isWrite) {
        if (os->readOnly) {
          terminateStateOnError(state, "memory error: object read only", ReadOnly);
        } else {
          //Todo: Implement for writes.  Need to actually apply psn, and
          //add new method for applying poison on write for constant
          //offsets.  For now, it's OK to leave this blank as we fall-through to the
          //older slower logic.
	  
          //ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          //wos->write(offset, value);
          //wos->applyPsnOnWrite(offset,value);
        }
      } else {
        ref<Expr> result = os->read(offset, type);

        //ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        //wos->applyPsnOnRead(offset); //Not needed for const offset
        if (interpreterOpts.MakeConcreteSymbolic)
          result = replaceReadWithSymbolic(state, result);
        bindLocal(target, state, result);
        return;
      }
    }
    //------------------End new fast path
    double T5 = util::getWallTime();
    if (MaxSymArraySize && mo->size>=MaxSymArraySize) {
      address = toConstant(state, address, "max-sym-array-size");
    }
    //LOG_TASE("%lf seconds in T5 \n", util::getWallTime() - T5);LOG_FLUSH();
    
    ref<Expr> offset;
    if (CE) {
      if (  CE->getZExtValue() + bytes <= mo->address + mo->size) {
        offset = ConstantExpr::create( CE->getZExtValue() - mo->address, Context::get().getPointerWidth());
      } else  {
        std::string ss;
        llvm::raw_string_ostream tmp(ss);
        address->print(tmp);
        std::cout << "Could not resolve address to MO: " << tmp.str() << "\n";
        std::cout << "Illegal offset in execute memory operation in " << reason << std::endl;
        std::exit(EXIT_FAILURE);
      }
    } else {
      offset = mo->getOffsetExpr(address);
    }
    bool inBounds;
    double T6 = util::getWallTime();
    //Fast path for TASE where offset is concrete
    if (CE) {
      //Should inequality be strictly less than?
      if (  CE->getZExtValue() + bytes <= mo->address + mo->size) {

        inBounds = true;
      } else { 
        //Code duplication: Remove me
        solver->setTimeout(coreSolverTimeout);
	ExecutionState dummy = ExecutionState(getDepCons(offset,false));
	//bool success = solver->mustBeTrue(state,
	bool success = solver->mustBeTrue(dummy,
                                          mo->getBoundsCheckOffset(offset, bytes),
                                          inBounds);
        solver->setTimeout(0);
        if (!success) {
          state.pc = state.prevPC;
          terminateStateEarly(state, "Query timed out (bounds check).");
          return;
        }
      }
    } else {
      solver->setTimeout(coreSolverTimeout);
      ExecutionState dummy = ExecutionState(getDepCons(offset,false));
      //bool success = solver->mustBeTrue(state,
      bool success = solver->mustBeTrue(dummy,
                                        mo->getBoundsCheckOffset(offset, bytes),
                                        inBounds);
      solver->setTimeout(0);
      if (!success) {
        state.pc = state.prevPC;
        terminateStateEarly(state, "Query timed out (bounds check).");
        return;
      }
    }
    //LOG_TASE("%lf seconds in T6 \n", util::getWallTime() - T6);LOG_FLUSH();
    if (inBounds) {
      const ObjectState *os = op.second;
      if (isWrite) {
        if (os->readOnly) {
          terminateStateOnError(state, "memory error: object read only",
                                ReadOnly);
        } else {
	  if (!isa<ConstantExpr> (offset)) {
	    //ABH: This is an optimization for cases where we're writing to an address specified
	    //by a symbolic expression.  If the expression for the address actually can only be
	    //one value, just use that and effectively concretize the address to avoid flushing
	    //and dealing with the symbolic pointer.  Does not lose any precision.
	    LOG_TASE("Symbolic write detected \n");
	    double tmp1 = util::getWallTime();
	    ExecutionState dummy = ExecutionState(getDepCons(offset,false));
	    std::vector<ref<Expr>> writeAddrs = getNPossibleValues(dummy, offset, 100);
	    LOG_TASE("%d addresses possible for writeAddrs \n", writeAddrs.size());
	    if (writeAddrs.size() == 1) {
	      LOG_TASE("Concretizing writeAddr \n");LOG_FLUSH();
	      offset = writeAddrs[0];
	    }
	    LOG_TASE("%lf seconds on concretizing symbolic write \n", util::getWallTime() - tmp1);LOG_FLUSH();
	  }
	  double tmp2 = util::getWallTime();
          ObjectState *wos = state.addressSpace.getWriteable(mo, os);
          wos->write(offset, value);
          wos->applyPsnOnWrite(offset,value);
	  //LOG_TASE("Spent 0x%lf seconds on tmp2 \n", util::getWallTime() - tmp2);LOG_FLUSH();
        }          
      } else {
	if (!isa<ConstantExpr> (offset)) {
	  LOG_TASE("Symbolic read detected \n");LOG_FLUSH();
	  //ABH: This is another optimization for TASE to avoid dealing with symbolic pointers.
	  //We basically look at all the possible values of the pointer and return a symbolic var X
	  //constrained such that (ptr == ptrVal1 AND X == *ptrVal1) || (ptr == ptrVal2 AND X == *ptrVal2) || ... 
	  double start = util::getWallTime();
	  ref<Expr> result = handleSymbolicOffset(offset, os,  type);
	  LOG_TASE("Spent %lf seconds in handleSymbolicOffset \n", util::getWallTime() - start);
	  bindLocal(target, state, result);
	} else {
	  ref<Expr> result = os->read(offset, type);
	  ObjectState *wos = state.addressSpace.getWriteable(mo, os);
	  wos->applyPsnOnRead(offset);
	  if (interpreterOpts.MakeConcreteSymbolic)
	    result = replaceReadWithSymbolic(state, result);
	  bindLocal(target, state, result);
	}
      }
      
      return;
    }
  } 
  
  // we are on an error path (no resolution, multiple resolution, one
  // resolution with out of bounds)
  
  ResolutionList rl;  
  solver->setTimeout(coreSolverTimeout);
  bool incomplete = state.addressSpace.resolve(state, solver, address, rl,
                                               0, coreSolverTimeout);
  solver->setTimeout(0);

  // XXX there is some query wasteage here. who cares?
  ExecutionState *unbound = &state;
  
  for (ResolutionList::iterator i = rl.begin(), ie = rl.end(); i != ie; ++i) {
    const MemoryObject *mo = i->first;
    const ObjectState *os = i->second;
    ref<Expr> inBounds = mo->getBoundsCheckPointer(address, bytes);
    
    StatePair branches = fork(*unbound, inBounds, true);
    ExecutionState *bound = branches.first;

    // bound can be 0 on failure or overlapped 
    if (bound) {
      if (isWrite) {
        if (os->readOnly) {
          terminateStateOnError(*bound, "memory error: object read only",
                                ReadOnly);
        } else {
          ObjectState *wos = bound->addressSpace.getWriteable(mo, os);
          wos->write(mo->getOffsetExpr(address), value);
          wos->applyPsnOnWrite(mo->getOffsetExpr(address), value);
        }
      } else {
        ref<Expr> result = os->read(mo->getOffsetExpr(address), type);
        ObjectState *wos = bound->addressSpace.getWriteable(mo, os);
        wos->applyPsnOnRead(mo->getOffsetExpr(address));  //Todo: ABH - should this be on os instead of wos?
        bindLocal(target, *bound, result);
      }
    }

    unbound = branches.second;
    if (!unbound)
      break;
  }

  // XXX should we distinguish out of bounds and overlapped cases?
  if (unbound) {
    if (incomplete) {
      terminateStateEarly(*unbound, "Query timed out (resolve).");
    } else {
      terminateStateOnError(*unbound, "memory error: out of bound pointer", Ptr,
                            NULL, getAddressInfo(*unbound, address));
      std::exit(EXIT_FAILURE);
    }
  }
}

void Executor::concretizeGPRArgs( unsigned int argNum, const char * reason) {

  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);
  ref<Expr> arg4Expr = target_ctx_gregs_OS->read(GREG_RCX * 8, Expr::Int64);
  ref<Expr> arg5Expr = target_ctx_gregs_OS->read(GREG_R8 * 8, Expr::Int64);
  ref<Expr> arg6Expr = target_ctx_gregs_OS->read(GREG_R9 * 8, Expr::Int64);

  LOG_TASE("WARNING: Concretizing GPR args for %s \n", reason);
  
  if (argNum == 0 || argNum > 7) {
    LOG_TASE("ERROR -- concretizeGPRArgs called with invalid number of args %u ", argNum)
    worker_error(Stopped, Running);
    exit(1);
  }

  if (argNum >= 1 ) {
    if (!isa<ConstantExpr>(arg1Expr)) {
      ref<Expr> ConcArg1Expr = toConstant(*GlobalExecutionStatePtr, arg1Expr, reason);
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDI].u64,ConcArg1Expr); 
    }
  }

  if (argNum >= 2 ) {
    if (!isa<ConstantExpr>(arg2Expr)) {
      ref<Expr> ConcArg2Expr = toConstant(*GlobalExecutionStatePtr, arg2Expr, reason);
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RSI].u64,ConcArg2Expr);
    }
  }

  if (argNum >= 3 ) {
    if (!isa<ConstantExpr>(arg3Expr)) {
      ref<Expr> ConcArg3Expr = toConstant(*GlobalExecutionStatePtr, arg3Expr, reason);
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDX].u64,ConcArg3Expr);
    }
  }

  if (argNum >= 4 ) {
    if (!isa<ConstantExpr>(arg4Expr)) {
      ref<Expr> ConcArg4Expr = toConstant(*GlobalExecutionStatePtr, arg4Expr, reason);
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RCX].u64,ConcArg4Expr);
    }
  }
  
  if (argNum >= 5 ) {
    if (!isa<ConstantExpr>(arg5Expr)) {
      ref<Expr> ConcArg5Expr = toConstant(*GlobalExecutionStatePtr, arg5Expr, reason);
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R8].u64,ConcArg5Expr);
    }
  }

  if (argNum >= 6 ) {
    if (!isa<ConstantExpr>(arg6Expr)) {
      ref<Expr> ConcArg6Expr = toConstant(*GlobalExecutionStatePtr, arg6Expr, reason);
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R9].u64,ConcArg6Expr);
    }
  }
  
  
}

void Executor::executeMakeSymbolic(ExecutionState &state, 
                                   const MemoryObject *mo,
                                   const std::string &name) {

  static int executeMakeSymbolicCalls = 0;  
  executeMakeSymbolicCalls++;

#ifdef TASE_OPENSSL
  if ( executeMakeSymbolicCalls == 1 ) {
    //Bootstrap multipass here for the very first round
    //before we hit a concretized writesocket call
    // if (modelDebug) {
    //   printf("Calling multipass_reset_round and multipass_start_round for first time \n");
    //   fflush(stdout);
    // }
    MOD_TASE("Calling multipass_reset_round and multipass_start_round for first time \n")
    
    multipass_reset_round(true);
    multipass_start_round(this, false);
  }
#endif
  
  // if(modelDebug) {
  //   printf("Calling executeMakeSymbolic on name %s \n", name.c_str());
  //   std::cout.flush();
  // }
  MOD_TASE("Calling executeMakeSymbolic on name %s \n", name.c_str())
  
  bool unnamed = (name == "unnamed") ? true : false;
  // Create a new object state for the memory object (instead of a copy).
  
  std::string array_name = get_unique_array_name(name);
  // if (modelDebug) {
  //   printf("DBG executeMakeSymbolic: Encountered unique name for %s \n", array_name.c_str());
  //   std::cout.flush();
  // }
  MOD_TASE("DBG executeMakeSymbolic: Encountered unique name for %s \n", array_name.c_str())
    
  //See if we have an assignment
  const klee::Array *array = NULL;
  if (!unnamed && prevMPA.bindings.size() != 0) {
    array = prevMPA.getArray(array_name);
  }
  
  bool multipass = false;
  if (array != NULL) {
    // if (taseDebug) {
    //   printf("Found concretization \n");
    //   std::cout.flush();
    // }
    DBG_TASE("Found concretization \n")
    //CVDEBUG("Multi-pass: Concretization found for " << array_name);
    multipass = true;
  } else {
    // if (!unnamed && taseDebug) {
    //   printf("Didn't find concretization \n");
    //   std::cout.flush();
    // }
    if( !unnamed ) {
      DBG_TASE("Didn't find concretization \n")
    }
    
    array = arrayCache.CreateArray(array_name, mo->size);
    round_symbolics.push_back(array);
  }
  
  bindObjectInState(state, mo, false, array, true /*forTase*/);

  std::vector<unsigned char> *bindings = NULL;
  if (pass_count > 0 && multipass) {
    bindings = prevMPA.getBindings(array_name);
    
    if (!bindings || bindings->size() != mo->size) {
      LOG_TASE("Bindings mismatch in executeMakeSymbolic; terminating \n")
      worker_error(Stopped, Running);
      exit(1);
    } else {
      const klee::ObjectState *os = state.addressSpace.findObject(mo);
      klee::ObjectState *wos = state.addressSpace.getWriteable(mo, os);
      assert(wos && "Writeable object is NULL!");
      unsigned idx = 0;
      for (std::vector<unsigned char>::iterator it = bindings->begin();  it!= bindings->end(); it++) {
	wos->write8(idx, *it);
	idx++;
      }
    }
  } else {
    // if (modelDebug) {
    //   printf("DBG executeMakeSymbolic: Created symbolic var for %s \n", name.c_str());
    //   std::cout.flush();
    // }
    MOD_TASE("DBG executeMakeSymbolic: Created symbolic var for %s \n", name.c_str())
    state.addSymbolic(mo, array);
    multipass_symbolic_vars++;
  }

}

extern "C" void target_exit() {
  LOG_TASE("Target exited \n");
  LOG_TASE("Executed %lu total interp instructions \n", instCtr);
  LOG_TASE("Execution State has stack size %lu \n", GlobalExecutionStatePtr->stack.size());
  LOG_TASE("Found %d calls to solver in fork \n", forkSolverCalls);
  LOG_FLUSH();
  //  tase_exit();
  exit(0);
}


uint64_t init_trap_RIP = 0;

extern "C" void klee_interp () {
  uint64_t interpCtr_init = interpCtr;
  init_trap_RIP = target_ctx_gregs[GREG_RIP].u64;

  if (measureTime) 
    interp_enter_time = util::getWallTime();
  
  DBG_TASE("---------------ENTERING KLEE_INTERP ----------------------\n")
  
  abort_info.classify_and_count();
  abort_info.print();

  ex_state.update( abort_info.type );
  
  if( ex_state == EXECUTION_STATE::BOUNCEBACK ) {
    DBG_TASE("Attempting to bounceback to native execution at RIP %lx and tran_max = %ld\n", target_ctx_gregs[GREG_RIP].u64, tran_max)
    return;
  }

  DBG_TASE("Not attempting to bounceback to native execution at RIP 0x%lx \n", target_ctx_gregs[GREG_RIP].u64);
  LOG_FLUSH();
  
  target_ctx_gregs[GREG_R14].u64 = 0; //Kill r14 because it's only used for instrumentation
  GlobalInterpreter->klee_interp_internal();
  
  if (measureTime) 
    measure_interp_time(interpCtr_init, target_ctx_gregs[GREG_R15].u64);

  tran_max = tranMaxArg;
  return; //Returns to loop in klee main
}


bool Executor::resumeNativeExecution() {
  return false;
}


//This function's purpose is to take a context from native execution 
//and return an llvm function for interpretation.  May interpret through
//a single instruction, or a full basic block.
KFunction * findInterpFunction (tase_greg_t * registers, KModule * kmod) {

  //  if (taseDebug) {
    //    printf("Attempting to find interp function \n");
    //    fflush(stdout);
  //  }
  DBG_TASE("Attempting to find interp function \n")
  
  KFunction * KInterpFunction;
  uint64_t nativePC = registers[GREG_RIP].u64;

  auto it = IR_KF_Map.find(nativePC);
  if (it != IR_KF_Map.end()) {
    KInterpFunction = it->second;
  } else {
    std::stringstream converter;
    converter << std::hex << nativePC;
    llvm::Function * interpFn = interpModule->getFunction("interp_fn_" + converter.str());
    KInterpFunction = kmod->functionMap[interpFn];
    IR_KF_Map.insert(std::make_pair(nativePC, KInterpFunction));
  }
  
  if (!KInterpFunction) {
    LOG_TASE("Unable to find interp function for entrypoint PC 0x%lx \n", nativePC)
    worker_error(Stopped, Running);
    exit(1);
  } else {
    DBG_TASE("Found interp function \n")
  }
  return KInterpFunction;
}
//Here's the interface expected for the llvm interpretation function.

// void @interp_fn_PCValHere( %tase_greg_t * %target_ctx_ptr) {
//; Emulate the native code modeled in the function, including an
//; updated program counter.  %target_ctx_ptr will take the initial tase_greg_t ctx,
//; and the necessary interpretation will occur in-place at the ctx pointed to. Also need 
//; to perform loads and stores to main memory.  By this point, an llvm load/store to
//; a given address in the interpreter will result in a load/store from/to the actual
//; native memory address.
// }

//Just an external trap for making a byte symbolic
void Executor::make_byte_symbolic_model() {
  //  printf("Hit make_byte_symbolic_model on addr 0x%lx \n", target_ctx_gregs[GREG_RDI].u64);
  LOG_TASE("Hit make_byte_symbolic_model on addr 0x%lx \n", target_ctx_gregs[GREG_RDI].u64)
  
  uint64_t addr = target_ctx_gregs[GREG_RDI].u64;
  tase_make_symbolic_internal(addr, 1, "external_request");
  if ( target_ctx.poisonSize == 4 ) {
    //    printf("creating second poison location for DWORD Poison at addr %lx\n", addr+sizeof(uint16_t));
    //    fflush(stdout);
    LOG_TASE("creating second poison location for DWORD Poison at addr %lx\n", addr+sizeof(uint16_t))
    tase_make_symbolic_internal(addr + sizeof(uint16_t), 1, "external_request_word_2");
  }

  //fake a ret
  uint64_t retAddr = *((uint64_t *) target_ctx_gregs[GREG_RSP].u64);
  target_ctx_gregs[GREG_RIP].u64 = retAddr;
  target_ctx_gregs[GREG_RSP].u64 += 8;
}

extern std::vector<ref<Expr>> trainInputExprs;
//Populate a buffer at addr with len bytes of unconstrained symbolic data.
//We make the symbolic memory object at a malloc'd address and write the bytes to addr.
int trainInputExprCtr = 0;
void Executor::tase_make_symbolic_internal(uint64_t addr, uint64_t len, const char * name)  {
  if (addr %2 != 0)
    LOG_TASE("WARNING: tase_make_symbolic_internal called on unaligned object \n")    

  void * buf = malloc(len);
  MemoryObject * bufMO = memory->allocateFixed((uint64_t) buf, len,  NULL);
  std::string nameString = name;
  bufMO->name = nameString;
  executeMakeSymbolic(*GlobalExecutionStatePtr, bufMO, name);
  const ObjectState * constBufOS = GlobalExecutionStatePtr->addressSpace.findObject(bufMO);
  ObjectState * bufOS = GlobalExecutionStatePtr->addressSpace.getWriteable(bufMO, constBufOS);

  for (uint64_t i = 0; i < len; i++) {
    tase_helper_write(addr + i, bufOS->read(i, Expr::Int8));
  }
  //If we've started our verification test, record all the times we have to make a key symbolic.
  //This needs to be gated because, if for example we're verifying msg 100, we had to
  //replay through msgs 0-99 and don't count those tase_make_symbolic calls for the purposes
  //of getting the keys for the new path verifying msg 100.
  //Logic is gated to "input!!" because that's the symbolic variable name of keys in tetrinet
  std::string nameStr(name);
  LOG_TASE("DBG1234: name is %s \n", name);LOG_FLUSH();
  if (updateSyntheticPaths && verTestType == VerTestType::SINGLEMSGVER && inPriorityTest && nameStr.find("input!!") != std::string::npos ) {
    LOG_TASE("Adding keystroke to trainInputExprs for time %d \n",trainInputExprCtr );LOG_FLUSH();
    ref<Expr> keyStroke = tase_helper_read(addr, len);
    trainInputExprs.push_back(keyStroke);
    trainInputExprCtr++;
  }
  
}

void Executor::tase_make_symbolic_bytewise(uint64_t addr, uint64_t len, const char * name) {
  for (uint64_t i = 0; i < len; i++) {
    std::string s = "_byte_" + std::to_string(i); 
    std::string varName = std::string(name) + s;

    tase_make_symbolic_internal(addr + i, 1, varName.c_str());
  }		       
}

/*void Executor::model_sb_disabled() {
  target_ctx_gregs[GREG_RIP].u64 = target_ctx_gregs[GREG_R15].u64;
  }*/

void Executor::model_sb_reopen() {
  target_ctx_gregs[GREG_RIP].u64 = target_ctx_gregs[GREG_RAX].u64;
}


//Todo: Double check the edge cases and make sure we handle
//buffers allocated at odd addresses.
bool Executor::isBufferEntirelyConcrete(uint64_t addr, int size) {
  //Fast path
  bool definitelyConcrete = !tase_buf_has_taint((void *) addr, size);
  if (definitelyConcrete)
    return true;
  
  //Slow path
  uint64_t byteItr = (uint64_t) addr;
  for (int i = 0; i < size; i++) {
    ref<Expr> byteExpr = tase_helper_read(byteItr+i, 1);
    if ( !isa<ConstantExpr>(byteExpr) )
      return false;	
  }
  return true;
}
/*
ref<Expr> Executor::tase_simplify_zext(ref<Expr> input) {
  if (isa<ZExtExpr> (input)) {
    
  }
  
}
*/
//Todo:  Make fastpath lookup where we leverage poison checking instead of
//full lookup.
//tase_helper_read: This func exists because reads and writes to
//object states in klee need to happen as offsets to buffers that have
//already been allocatated.  
ref<Expr> Executor::tase_helper_read (uint64_t addr, uint8_t byteWidth) {

  ref<Expr> addrExpr = ConstantExpr::create(addr, Expr::Int64);

  //Find a better way to do this.  Using logic from Executor::executeMemoryOperation
  //begin gross------------------
  ObjectPair op;
  bool success;
  
  if (!(GlobalExecutionStatePtr->addressSpace.resolveOne(*GlobalExecutionStatePtr,solver,addrExpr, op, success))) {
    //    printf("ERROR in tase_helper_read: Couldn't resolve addr to fixed value \n");
    LOG_TASE("ERROR in tase_helper_read: Couldn't resolve addr to fixed value \n")
    std::cout.flush();
    std::exit(EXIT_FAILURE);
  }
  ref<Expr> offset = op.first->getOffsetExpr(addrExpr);
  //end gross----------------------------

  ref<Expr> returnVal;
  ObjectState *wos = GlobalExecutionStatePtr->addressSpace.getWriteable(op.first, op.second);
  
  switch( byteWidth ) {
  case 1:
    returnVal = wos->read(offset, Expr::Int8);
    break;
  case 2:
    returnVal = wos->read(offset, Expr::Int16);
    break;
  case 4:
    returnVal = wos->read(offset, Expr::Int32);
    break;
  case 8:
    returnVal = wos->read(offset, Expr::Int64);
    break;
  default:
    LOG_TASE("Unrecognized byteWidth in tase_helper_read: %u \n", byteWidth);
    std::exit(EXIT_FAILURE);
  } 


  wos->applyPsnOnRead(offset);
  return returnVal;
}


template<typename T1, typename T2, typename... Ts>
bool Executor::tase_map(const std::string& name, T1 t1, T2 t2, Ts... ts){
  bool a = tase_map(t1, name) & tase_map(name, t2, ts...);
  if ( !a ) {
    //    std::cout << "error mapping buffer: " << name << std::endl;
    LOG_TASE("error mapping buffer: %s", name)
  }

  return a;
}

// for things like ptr into buffer for start/end/current position...
template<typename T>
bool Executor::tase_map(const T*& t, const std::string& name){
  bool a = tase_map_buf((uint64_t) &t, sizeof(T*), name);
  if( !a ) {
    LOG_TASE("Error mapping buffer: %s", name.c_str())
  }
  return a;
}

template<typename T>
bool Executor::tase_map(T* const & t, const size_t& size, const std::string& name){
  bool a = tase_map_buf((uint64_t) &t, sizeof(T*), name);
  bool b = tase_map_buf((uint64_t) t, sizeof(T) * size, name);
  if ( !a || !b ) {
    LOG_TASE("Error mapping buffer: %s - generic pointer %s size %ld\n", name.c_str(), !a ? "a" : "b", size*sizeof(T)) 
  }
  return a && b;
}

template bool Executor::tase_map<char>(char* const & t, const size_t& size, const std::string& name); // force instantiation
//template ObjectState *  Executor::tase_map<unsigned char>(unsigned char* const & t, const size_t& size); // force instantiation

// assume null-terminated
template<>
bool Executor::tase_map(char* const & t, const std::string& name){
  auto a = t == NULL ? tase_map_buf((uint64_t) &t, sizeof(char*), name) : tase_map(t, strlen(t)+1, name);
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s - %s\n", name.c_str(), t == NULL ? "NULL" : "non-NULL")
  }
  return a;
}

template<>
bool Executor::tase_map(void* const & t, const std::string& name){
  bool a = tase_map_buf((uint64_t) &t, sizeof(void*), name);
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s\n", name.c_str())
  }
  return a;
}

typedef size_t (read_t)(FILE*, unsigned char*, size_t);
typedef size_t (write_t)(FILE*, const unsigned char *, size_t);
typedef off_t (seek_t)(FILE*, off_t, int);

template<>
bool Executor::tase_map(read_t* const& t, const std::string& name){
  bool a = tase_map_buf((uint64_t)&t, sizeof(read_t*), name);
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s\n", name.c_str())
  }
  return a;
}

template<>
bool Executor::tase_map(write_t* const& t, const std::string& name){
  bool a = tase_map_buf((uint64_t)&t, sizeof(write_t*), name);
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s\n", name.c_str())      
  }
  return a;
}

template<>
bool Executor::tase_map(seek_t* const& t, const std::string& name){
  bool a = tase_map_buf((uint64_t) &t, sizeof(seek_t*), name);
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s\n", name.c_str())
  }
  return a;
}

// ptr default
//template<typename T>
/*bool Executor::tase_map(const T*& t){
  auto x = tase_map_buf((uint64_t) &t, sizeof(t));
  return t == NULL ? x : tase_map_buf((uint64_t) t, sizeof(T));
}*/

// default
template<typename T>
bool Executor::tase_map(const T& t, const std::string& name){
  bool a = tase_map_buf((uint64_t) &t, sizeof(t), name);
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s\n", name.c_str())
  }
  return a;
}

template bool Executor::tase_map<uint64_t>(const uint64_t&, const std::string& name);


template<>
bool Executor::tase_map(FILE* const & t, const std::string& name){
  bool a = tase_map_buf((uint64_t) &t, sizeof(FILE*), name);
    a &= (t == NULL ? a : tase_map(*t, name));
  if ( !a ) {
    LOG_TASE("Error mapping buffer: %s\n", name.c_str())    
  }
  return a;
}

/*template<>
bool Executor::tase_map(const FILE& t){
  tase_map(t.flags, t.rpos, t.rend, t.close, t.wend, t.wpos, t.mustbezero_1, t.wbase, t.read, t.write, t.seek);
  tase_map(t.buf, t.buf_size);
  return tase_map(t.prev, t.next, t.fd, t.pipe_pid, t.lockcount, t.mode, t.lock, t.lbf, t.cookie, t.off, t.getln_buf,
           t.mustbezero_2, t.shend, t.shlim, t.shcnt, t.prev_locked, t.next_locked, t.locale);
}*/

//Todo -- make this play nice with our alignment requirements
 bool Executor::tase_map_buf(uint64_t addr, size_t size, const std::string& name) {
   if( size % 8 != 0 ) {
     size_t nsize = 8*(size / 8);
     size = nsize < size ? nsize + 8 : nsize;
   }
   return addExternalObjectCheck(*GlobalExecutionStatePtr, (void *) addr, size, false, name, true);
   //MemoryObject * MOres = addExternalObject(*GlobalExecutionStatePtr, (void *) addr, size, false, name, true);
  //  const ObjectState * OSConst = GlobalExecutionStatePtr->addressSpace.findObject(MOres);
  //  ObjectState * OSres = GlobalExecutionStatePtr->addressSpace.getWriteable(MOres, OSConst);
  //  OSres->concreteStore = (uint8_t *) addr;
   // return OSres;
}

//Todo: See if we can make this faster with the poison checking scheme.
//tase_helper_write: Helper function similar to tase_helper_read
//that helps us avoid rewriting the offset-lookup logic over and over.
void Executor::tase_helper_write(uint64_t addr, ref<Expr> val) {
  
  ref<Expr> addrExpr = ConstantExpr::create(addr, Expr::Int64);

  //Find a better way to do this.  Using logic from Executor::executeMemoryOperation
  //begin gross------------------
  ObjectPair op;
  bool success;
  if (! GlobalExecutionStatePtr->addressSpace.resolveOne(*GlobalExecutionStatePtr,solver,addrExpr, op, success) ) {
    LOG_TASE("ERROR in tase_helper_write: Couldn't resolve addr to fixed value \n")
    std::exit(EXIT_FAILURE);
  }

  ref<Expr> offset = op.first->getOffsetExpr(addrExpr);
  //end gross----------------------------
  ObjectState *wos = GlobalExecutionStatePtr->addressSpace.getWriteable(op.first, op.second);

  wos->write(offset, val);
  wos->applyPsnOnWrite(offset, val);

}



//static int model_malloc_calls = 0;



/*Macro for (M)odeled (F)unction (E)ntries
#define MFE(x, y) fnModelMap.insert(std::make_pair( (uint64_t)   &x , &klee::Executor::y )); \
fnModelMap.insert(std::make_pair( (uint64_t)   &x  + trap_off, &klee::Executor::y ))*/

/* Example for MFE(calloc_tase, model_calloc):
fnModelMap.insert(std::make_pair( (uint64_t) &calloc_tase , &klee::Executor::model_calloc ));
fnModelMap.insert(std::make_pair( (uint64_t) &calloc_tase + trap_off, &klee::Executor::model_calloc ));
*/

void Executor::loadFnModelMap() {
  fnModelMap = {
  //MAVLink modeled fns
  {(uint64_t) &mavlink_write_tase,  &Executor::model_mavlink_write_tase},
  {(uint64_t) &peekChannelState, &Executor::model_peek_channel_state},
		
  //TetriNET modeled fns
  {(uint64_t) &srand_tase,  &Executor::model_srand},
  {(uint64_t) &conn_tase,  &Executor::model_tetri_conn},
  {(uint64_t) &ktest_write_tase,  &Executor::model_tetri_ktest_write},
  {(uint64_t) &sgets_tase,  &Executor::model_tetri_sgets},
  {(uint64_t) &shutdown_tase,  &Executor::model_tetri_shutdown},
  {(uint64_t) &vsnprintf_tase, &Executor::model_tetri_vsnprintf},

  {(uint64_t) &calloc_tase,  &Executor::model_calloc},
  {(uint64_t) &__ctype_b_loc,  &Executor::model___ctype_b_loc},
  {(uint64_t) &__ctype_tolower_loc,  &Executor::model___ctype_tolower_loc},
  {(uint64_t) &__errno_location,  &Executor::model___errno_location},
  //  {(uint64_t) &exit_tase_shim,  &Executor::model_exit_tase_success},
  {(uint64_t) &exit_tase,  &Executor::model_exit_tase},
  {(uint64_t) &fclose,  &Executor::model_fclose},
  {(uint64_t) &fcntl,  &Executor::model_fcntl},
  {(uint64_t) &feof_tase,  &Executor::model_feof},
  {(uint64_t) &ferror_tase,  &Executor::model_ferror},
  {(uint64_t) &fflush_tase,  &Executor::model_fflush},
  //  {(uint64_t) &fflush_tase_shim, &Executor::model_fflush},
  {(uint64_t) &fflush_unlocked, &Executor::model_fflush_unlocked},
  {(uint64_t) &fgets,  &Executor::model_fgets},
  {(uint64_t) &fileno_tase,  &Executor::model_fileno},
  {(uint64_t) &fopen_tase,  &Executor::model_fopen},
  {(uint64_t) &fopen64,  &Executor::model_fopen64},
  {(uint64_t) &fclose_tase, &Executor::model_fclose},
  {(uint64_t) &fread_tase,  &Executor::model_fread},
  {(uint64_t) &fread_unlocked_tase,  &Executor::model_fread_unlocked}, //double check against model_fread
  //  {(uint64_t) &free,  &Executor::model_free},
  {(uint64_t) &free_tase,  &Executor::model_free},
  //  {(uint64_t) &free_tase_shim, &Executor::model_free},
  {(uint64_t) &freopen_tase,  &Executor::model_freopen},
  {(uint64_t) &fseek_tase,  &Executor::model_fseek},
  {(uint64_t) &ftell_tase,  &Executor::model_ftell},
  {(uint64_t) &fwrite_tase,  &Executor::model_fwrite},
  {(uint64_t) &fwrite_unlocked,  &Executor::model_fwrite}, //double check against model_fwrite
  //  {(uint64_t) &getc_unlocked,  &Executor::model_getc_unlocked},
  {(uint64_t) &getc_unlocked_tase,  &Executor::model_getc_unlocked},
  //  {(uint64_t) &getc_unlocked_tase_shim, &Executor::model_getc_unlocked},
  {(uint64_t) &getegid,  &Executor::model_getegid},
  {(uint64_t) &getenv,  &Executor::model_getenv},
  {(uint64_t) &geteuid,  &Executor::model_geteuid},
  {(uint64_t) &getgid,  &Executor::model_getgid},
  {(uint64_t) &gethostbyname,  &Executor::model_gethostbyname},
  {(uint64_t) &getpid,  &Executor::model_getpid},
  {(uint64_t) &gettimeofday,  &Executor::model_gettimeofday},
  {(uint64_t) &getuid,  &Executor::model_getuid},
  {(uint64_t) &gmtime,  &Executor::model_gmtime},
  {(uint64_t) &isatty_tase,  &Executor::model_isatty},
  {(uint64_t) &__isoc99_sscanf,  &Executor::model___isoc99_sscanf},
  {(uint64_t) &make_byte_symbolic,  &Executor::make_byte_symbolic_model},
  //  {(uint64_t) &malloc,  &Executor::model_malloc},
  {(uint64_t) &malloc_tase,  &Executor::model_malloc},
  //  {(uint64_t) &malloc_tase_shim, &Executor::model_malloc},
  //  {(uint64_t) &memcpy,  &Executor::model_memcpy_tase},
  {(uint64_t) &memcpy_tase,  &Executor::model_memcpy_tase},
  {(uint64_t) &posix_fadvise_tase,  &Executor::model_posix_fadvise},
  {(uint64_t) &usleep_tase, &Executor::model_usleep},
  {(uint64_t) &putchar_tase,  &Executor::model_putchar},
  {(uint64_t) &printf_tase,  &Executor::model_printf},
		//  {(uint64_t) &vsnprintf_tase, &Executor::model_vsnprintf}, //ALTERED FOR TETRINET - ABH
  {(uint64_t) &vasprintf_tase, &Executor::model_vasprintf},
  {(uint64_t) &mbsrtowcs, &Executor::model_mbsrtowcs},
  {(uint64_t) &setlocale, &Executor::model_setlocale},
  {(uint64_t) &sigemptyset, &Executor::model_sigemptyset},
  {(uint64_t) &sigaddset, &Executor::model_sigaddset},
  {(uint64_t) &sigprocmask, &Executor::model_sigprocmask},
  {(uint64_t) &sigaction, &Executor::model_sigaction},
  {(uint64_t) &__printf_chk,  &Executor::model___printf_chk},
  {(uint64_t) &puts_tase,  &Executor::model_puts},
  //  {(uint64_t) &puts_tase_shim, &Executor::model_puts},

  //{(uint64_t) &read,  &Executor::model_read}, //Model doesn't exist yet.  fixme.
  //  {(uint64_t) &realloc,  &Executor::model_realloc},
  {(uint64_t) &realloc_tase,  &Executor::model_realloc},
  //  {(uint64_t) &realloc_tase_shim, &Executor::model_realloc},
  {(uint64_t) &rewind_tase,  &Executor::model_rewind},
  //  {(uint64_t) &sb_disabled,  &Executor::model_sb_disabled},
  //  {(uint64_t) &sb_reopen,  &Executor::model_sb_reopen},
  //  {(uint64_t) &sb_eject, &Executor::model_sb_eject},
  {(uint64_t) &sprintf_tase,  &Executor::model_sprintf},
  {(uint64_t) &sscanf,  &Executor::model___isoc99_sscanf},//Check to make sure it's OK to model with C99
  {(uint64_t) &stat,  &Executor::model_stat},
  //{(uint64_t) &target_exit,  &Executor::model_target_exit}, //Special case. fixme. //Doesn't look like we call target_exit anymore.
  {(uint64_t) &time,  &Executor::model_time},
  {(uint64_t) &fprintf_tase, &Executor::model_fprintf},
//  {(uint64_t) &vfprintf,  &Executor::model_vfprintf},
  {(uint64_t) &write_tase,  &Executor::model_write},
  {(uint64_t) &ioctl, &Executor::model_ioctl},
  {(uint64_t) &strtof_tase,  &Executor::model_strtof},
  {(uint64_t) &strtod_tase,  &Executor::model_strtod},
  {(uint64_t) &strtold_tase,  &Executor::model_strtold},
  {(uint64_t) &strtol_tase,  &Executor::model_strtol},
  {(uint64_t) &strtoll_tase,  &Executor::model_strtoll},
  {(uint64_t) &strtoul_tase,  &Executor::model_strtoul},
  {(uint64_t) &strtoull_tase,  &Executor::model_strtoull},
  {(uint64_t) &strtoimax_tase,  &Executor::model_strtoimax},
  {(uint64_t) &strtoumax_tase,  &Executor::model_strtoumax},

  {(uint64_t) &wcstof_tase,  &Executor::model_wcstof},
  {(uint64_t) &wcstod_tase,  &Executor::model_wcstod},
  {(uint64_t) &wcstold_tase,  &Executor::model_wcstold},
  {(uint64_t) &wcstol_tase,  &Executor::model_wcstol},
  {(uint64_t) &wcstoll_tase,  &Executor::model_wcstoll},
  {(uint64_t) &wcstoul_tase,  &Executor::model_wcstoul},
  {(uint64_t) &wcstoull_tase,  &Executor::model_wcstoull},
  {(uint64_t) &wcstoumax_tase,  &Executor::model_wcstoumax},
  {(uint64_t) &wcstoimax_tase,  &Executor::model_wcstoimax},

 // {(uint64_t) &a_ctz_64_tase,  &Executor::model_a_ctz_64},
 // {(uint64_t) &a_clz_64_tase,  &Executor::model_a_clz_64},

  {(uint64_t) &tase_make_symbolic,  &Executor::model_tase_make_symbolic},

  {(uint64_t) &__pthread_self_tase,  &Executor::model___pthread_self},

#ifdef TASE_OPENSSL
  {(uint64_t) &AES_encrypt,  &Executor::model_AES_encrypt},
  {(uint64_t) &BIO_printf,  &Executor::model_BIO_printf},
  {(uint64_t) &ECDH_compute_key,  &Executor::model_ECDH_compute_key},
  {(uint64_t) &EC_KEY_generate_key,  &Executor::model_EC_KEY_generate_key},
  {(uint64_t) &EC_POINT_point2oct,  &Executor::model_EC_POINT_point2oct},
  {(uint64_t) &gcm_ghash_4bit,  &Executor::model_gcm_ghash_4bit},
  {(uint64_t) &gcm_gmult_4bit,  &Executor::model_gcm_gmult_4bit},
  {(uint64_t) &ktest_connect,  &Executor::model_ktest_connect},
  {(uint64_t) &ktest_master_secret,  &Executor::model_ktest_master_secret},
  {(uint64_t) &ktest_RAND_bytes,  &Executor::model_ktest_RAND_bytes},
  {(uint64_t) &ktest_RAND_pseudo_bytes,  &Executor::model_ktest_RAND_pseudo_bytes},
  {(uint64_t) &ktest_raw_read_stdin,  &Executor::model_ktest_raw_read_stdin},
  {(uint64_t) &ktest_readsocket,  &Executor::model_ktest_readsocket},
  {(uint64_t) &ktest_select,  &Executor::model_ktest_select},
  {(uint64_t) &ktest_start,  &Executor::model_ktest_start},
  {(uint64_t) &ktest_writesocket,  &Executor::model_ktest_writesocket},
  {(uint64_t) &OpenSSLDie,  &Executor::model_OpenSSLDie},
  {(uint64_t) &RAND_add,  &Executor::model_RAND_add},
  {(uint64_t) &RAND_load_file,  &Executor::model_RAND_load_file},
  {(uint64_t) &RAND_poll,  &Executor::model_RAND_poll},
  {(uint64_t) &SHA1_Final,  &Executor::model_SHA1_Final},
  {(uint64_t) &SHA1_Update,  &Executor::model_SHA1_Update},
  {(uint64_t) &SHA256_Final,  &Executor::model_SHA256_Final},
  {(uint64_t) &SHA256_Update,  &Executor::model_SHA256_Update},
  {(uint64_t) &select,  &Executor::model_select}, //Maybe move to generic section?
  {(uint64_t) &setsockopt,  &Executor::model_setsockopt},
  {(uint64_t) &shutdown,  &Executor::model_shutdown},
  {(uint64_t) &signal,  &Executor::model_signal},
  {(uint64_t) &socket,  &Executor::model_socket},
  {(uint64_t) &tls1_generate_master_secret,  &Executor::model_tls1_generate_master_secret},
#endif

  {(uint64_t) &__addsf3_tase, &Executor::model__addsf3},
  {(uint64_t) &__adddf3_tase, &Executor::model__adddf3},
  {(uint64_t) &__subsf3_tase, &Executor::model__subsf3},
  {(uint64_t) &__subdf3_tase, &Executor::model__subdf3},
  {(uint64_t) &__mulsf3_tase, &Executor::model__mulsf3},
  {(uint64_t) &__muldf3_tase, &Executor::model__muldf3},
  {(uint64_t) &__divsf3_tase, &Executor::model__divsf3},
  {(uint64_t) &__divdf3_tase, &Executor::model__divdf3},
  {(uint64_t) &__negsf2_tase, &Executor::model__negsf2},
  {(uint64_t) &__negdf2_tase, &Executor::model__negdf2},
  {(uint64_t) &__extendsfdf2_tase, &Executor::model__extendsfdf2},
  {(uint64_t) &__truncdfsf2_tase, &Executor::model__truncdfsf2},
  {(uint64_t) &__fixsfsi_tase, &Executor::model__fixsfsi},
  {(uint64_t) &__fixdfsi_tase, &Executor::model__fixdfsi},
  {(uint64_t) &__fixsfdi_tase, &Executor::model__fixsfdi},
  {(uint64_t) &__fixdfdi_tase, &Executor::model__fixdfdi},
  {(uint64_t) &__fixsfti_tase, &Executor::model__fixsfti},
  {(uint64_t) &__fixdfti_tase, &Executor::model__fixdfti},
  {(uint64_t) &__fixunssfsi_tase, &Executor::model__fixunssfsi},
  {(uint64_t) &__fixunsdfsi_tase, &Executor::model__fixunsdfsi},
  {(uint64_t) &__fixunssfdi_tase, &Executor::model__fixunssfdi},
  {(uint64_t) &__fixunsdfdi_tase, &Executor::model__fixunsdfdi},
  {(uint64_t) &__fixunssfti_tase, &Executor::model__fixunssfti},
  {(uint64_t) &__fixunsdfti_tase, &Executor::model__fixunsdfti},
  {(uint64_t) &__floatsisf_tase, &Executor::model__floatsisf},
  {(uint64_t) &__floatsidf_tase, &Executor::model__floatsidf},
  {(uint64_t) &__floatdisf_tase, &Executor::model__floatdisf},
  {(uint64_t) &__floatdidf_tase, &Executor::model__floatdidf},
  {(uint64_t) &__floattisf_tase, &Executor::model__floattisf},
  {(uint64_t) &__floattidf_tase, &Executor::model__floattidf},
  {(uint64_t) &__floatunsisf_tase, &Executor::model__floatunsisf},
  {(uint64_t) &__floatunsidf_tase, &Executor::model__floatunsidf},
  {(uint64_t) &__floatundisf_tase, &Executor::model__floatundisf},
  {(uint64_t) &__floatundidf_tase, &Executor::model__floatundidf},
  {(uint64_t) &__floatuntisf_tase, &Executor::model__floatuntisf},
  {(uint64_t) &__floatuntidf_tase, &Executor::model__floatuntidf},
  {(uint64_t) &__cmpsf2_tase, &Executor::model__cmpsf2},
  {(uint64_t) &__cmpdf2_tase, &Executor::model__cmpdf2},
  {(uint64_t) &__unordsf2_tase, &Executor::model__unordsf2},
  {(uint64_t) &__unorddf2_tase, &Executor::model__unorddf2},
  {(uint64_t) &__eqsf2_tase, &Executor::model__eqsf2},
  {(uint64_t) &__eqdf2_tase, &Executor::model__eqdf2},
  {(uint64_t) &__nesf2_tase, &Executor::model__nesf2},
  {(uint64_t) &__nedf2_tase, &Executor::model__nedf2},
  {(uint64_t) &__gesf2_tase, &Executor::model__gesf2},
  {(uint64_t) &__gedf2_tase, &Executor::model__gedf2},
  {(uint64_t) &__ltsf2_tase, &Executor::model__ltsf2},
  {(uint64_t) &__ltdf2_tase, &Executor::model__ltdf2},
  {(uint64_t) &__lesf2_tase, &Executor::model__lesf2},
  {(uint64_t) &__ledf2_tase, &Executor::model__ledf2},
  {(uint64_t) &__gtsf2_tase, &Executor::model__gtsf2},
  {(uint64_t) &__gtdf2_tase, &Executor::model__gtdf2},
  {(uint64_t) &__powisf2_tase, &Executor::model__powisf2},
  {(uint64_t) &__powidf2_tase, &Executor::model__powidf2},
  };
}



void Executor::printDebugInterpHeader() {
  LOG_TASE("------------------------------------------- \n");
  LOG_TASE("Entering interpreter for time %lu and instCtr %lu \n \n \n", interpCtr, instCtr);
  uint64_t rip = target_ctx_gregs[GREG_RIP].u64;
  LOG_TASE("RIP is 0x%lx\n", rip);
  LOG_TASE("Initial ctx BEFORE interpretation is \n");
  printCtx();
  LOG_TASE("\n")
}

void Executor::printDebugInterpFooter() {
  printCtx();
  LOG_TASE("Executor has %lu states \n", this->states.size() );
  LOG_TASE("Finished round %lu of interpretation. \n", interpCtr);
  LOG_TASE("-------------------------------------------\n");
}


// set based on poison_size and xmm vs zmm in main
extern "C" bool (*large_buf_has_taint)(const uint16_t*, const int);

//Fast-path check for poison tag in buffer.
//Todo -- double check the corner cases
extern "C" bool tase_buf_has_taint (const void * ptr, const int size) {
  // simpler construction: find end of original buffer
  // adjust start, loop until we're out of the original bounds, don't bother calculating size
  uint16_t * const end = (uint16_t*) (((uint64_t) ptr) + size);
  uint16_t * const start = ((uint64_t) ptr) % 2 == 1 ? (uint16_t *) ((uint64_t) ptr - 1 ) : (uint16_t *) ptr;

  if( target_ctx.poisonSize == 2 ) {
    for( uint16_t *x = start; end - x > 0; x++ ) {
      if( *x == poison_val )
	return true;
    }
  } else {
    for( uint16_t *x = start; end - x > 0; x += 2 ) {
      if( *x == poison_val && *(x+1) == poison_val )
	return true;
    }
  }
  return false;
  
  //  const int checkSize = ( ((uint8_t*) ptr + size + 1 ) - (uint8_t*) checkBase ) / 2;

  /*  if( checkSize > 4 ) { // more than 64 bits/8 btyes -> use xmm/ymms.  
    return large_buf_has_taint(checkBase, checkSize);
    }*/

  /*  if( target_ctx.poisonSize == 2 ) {
    for ( int i = 0; i < checkSize; i++ ) {
      if ( *( checkBase + i ) == poison_val )
        return true;
    }
  } else {
    for( int i = 0; i < checkSize/2; i++ ) {
      if( *( checkBase + 2*i ) == poison_val && *( checkBase + 2*i + 1 ) == poison_val )
	return true;
    }
  }
  
  return false;*/
}


// pretty much what we do in the springboard
extern "C" bool large_buf_has_taint_16_128(const uint16_t * checkBase, const int checkSize){
  const int x = checkSize % 8;
  const int rounds = x == 0 ? (checkSize / 8) : (checkSize / 8) + 1;

  // mask off leftovers
  const __m128i mask = _mm_setr_epi16( x == 0 ? 0xffff : 0x0000, x > 6 ? 0xffff : 0x0000, x > 5 ? 0xffff : 0x0000, x > 4 ? 0xffff : 0x0000,
				       x  > 3 ? 0xffff : 0x0000, x > 2 ? 0xffff : 0x0000, x > 1 ? 0xffff : 0x0000, x > 0 ? 0xffff : 0x0000  );

  __m128i acc;
  for(int i = 0; i < rounds; i++) {
    const __m128i a = _mm_load_si128((__m128i*)checkBase);
    const __m128i b = _mm_load_si128((__m128i*)&target_ctx.reference);
    
    __m128i cmp = _mm_cmpeq_epi16(a, b);
    if ( i == rounds - 1 ){
      cmp = _mm_or_si128(cmp, mask);
    }
    acc = _mm_or_si128(cmp, acc);
  }
  return _mm_testz_si128(acc, acc) != 0;
}


extern "C" bool large_buf_has_taint_32_128(const uint16_t * checkBase, const int checkSize){
  const int x = ( checkSize / 2 ) % 4;
  const int rounds = x == 0 ? (checkSize / 8) : (checkSize / 8) + 1;
  
  // mask off leftovers
  const __m128i mask = _mm_setr_epi32( x == 0 ? 0xffffffff : 0x00000000, x > 3 ? 0xffffffff : 0x00000000,
				       x > 2  ? 0xffffffff : 0x00000000, x > 1 ? 0xffffffff : 0x00000000 );

  __m128i acc;
  for(int i = 0; i < rounds; i++) {
    const __m128i a = _mm_load_si128((__m128i*)checkBase);
    const __m128i b = _mm_load_si128((__m128i*)&target_ctx.reference);
    __m128i cmp = _mm_cmpeq_epi32(a, b);
    if ( i == rounds - 1 ){
      cmp = _mm_or_si128(cmp, mask);
    }
    acc = _mm_or_si128(cmp, acc);
  }
  return _mm_testz_si128(acc, acc) != 0;
}



extern "C" bool large_buf_has_taint_32_256(const uint16_t * checkBase, const int checkSize){
  const int x = ( checkSize / 2 ) % 8;
  const int rounds = x ? (checkSize / 8) : (checkSize / 8) + 1;
  
  // mask off leftovers
  const __m256i mask = _mm256_setr_epi32( x == 0 ? 0xffffffff : 0x00000000, x > 7  ? 0xffffffff : 0x00000000,
					  x > 6  ? 0xffffffff : 0x00000000, x > 5  ? 0xffffffff : 0x00000000,
					  x > 4  ? 0xffffffff : 0x00000000, x > 3  ? 0xffffffff : 0x00000000,
					  x > 2  ? 0xffffffff : 0x00000000, x > 1  ? 0xffffffff : 0x00000000 );

  __m256i acc;
  for(int i = 0; i < rounds; i++) {
    const __m256i a = _mm256_load_si256((__m256i*)checkBase);
    const __m256i b = _mm256_load_si256((__m256i*)&target_ctx.reference);
    
    __m256i cmp = _mm256_cmpeq_epi32(a, b);
    if ( i == rounds - 1 ){
      cmp = _mm256_or_si256(cmp, mask);
    }
    acc = _mm256_or_si256(cmp, acc);
  }
  return _mm256_testz_si256(acc, acc) != 0;
}


extern "C" bool large_buf_has_taint_16_256(const uint16_t * checkBase, const int checkSize){
  const int rounds = checkSize % 16 == 0 ? (checkSize / 16) : (checkSize / 16) + 1;
  const int x = checkSize % 16;

  // mask off leftovers
  const __m256i mask = _mm256_setr_epi32( x == 0 ? 0xffffffff : (x > 15 ? 0x0000ffff : 0x00000000),
					  x > 14 ? 0xffffffff : (x > 13 ? 0x0000ffff : 0x00000000),
					  x > 12 ? 0xffffffff : (x > 11 ? 0x0000ffff : 0x00000000),
					  x > 10 ? 0xffffffff : (x > 9  ? 0x0000ffff : 0x00000000),
					  x > 8  ? 0xffffffff : (x > 7  ? 0x0000ffff : 0x00000000),
					  x > 6  ? 0xffffffff : (x > 5  ? 0x0000ffff : 0x00000000),
					  x > 4  ? 0xffffffff : (x > 3  ? 0x0000ffff : 0x00000000),
					  x > 2  ? 0xffffffff : (x > 1  ? 0x0000ffff : 0x00000000) );

  __m256i acc;
  for(int i = 0; i < rounds; i++) {
    const __m256i a = _mm256_load_si256((__m256i*)checkBase);  // 32-byte aligned load
    const __m256i b = _mm256_load_si256((__m256i*)&target_ctx.reference);
    __m256i cmp = _mm256_cmpeq_epi16(a, b);
    if ( i == rounds - 1 ){
      cmp = _mm256_or_si256(cmp, mask);
    }
    acc = _mm256_or_si256(cmp, acc);
  }
  return _mm256_testz_si256(acc, acc) != 0;
}


template < int I > inline int
scan (uint64_t target, uint64_t pattern, uint64_t mask) { return ((target >> 8 * I) & mask) == pattern ? I : -1; }

template<typename... Ts>
inline int scan(int I, Ts... ts) {
  switch(I){
  case 0: return scan<0>(ts...); break;
  case 1: return scan<1>(ts...); break;
  case 2: return scan<2>(ts...); break;
  case 3: return scan<3>(ts...); break;
  case 4: return scan<4>(ts...); break;
  case 5: return scan<5>(ts...); break;
  case 6: return scan<6>(ts...); break;
  case 7: return scan<7>(ts...); break;
  }
}

template <> inline int scan < 8 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }


template < int I, int J > inline int
scanleft (uint64_t target, uint64_t pattern, uint64_t mask);


template < int I > inline int
scanlefthelper (uint64_t target, uint64_t pattern, uint64_t mask) {
    return scanleft < I, I+1 > (target, pattern, mask);    
}

template <> inline int
scanlefthelper <8> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }

template < > inline int scanleft < 1, 0 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 2, 1 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 3, 2 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 4, 3 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 5, 4 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 6, 5 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 7, 6 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 8, 7 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }
template < > inline int scanleft < 8, 8 > (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; }

// scan full pattern, then scan partials
template < int I, int J > inline int
scanleft (uint64_t target, uint64_t pattern, uint64_t mask)
{
  return I < J ?
    ( scan < I > (target, pattern, mask) >=0 ? scan < I > (target, pattern, mask) : scanleft < I + 1, J > (target, pattern, mask) ) : 
     I == J && J < 8 ? scanlefthelper < I > (target, pattern << 8*I >> 8*I, mask << 8*I >> 8*I) : -1;
}


template< int I, int J > inline int
scanright (uint64_t target, uint64_t pattern, uint64_t mask);

template <> inline int scanright <1,1> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };
template <> inline int scanright <2,2> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };
template <> inline int scanright <3,3> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };
template <> inline int scanright <4,4> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };
template <> inline int scanright <5,5> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };
template <> inline int scanright <6,6> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };
template <> inline int scanright <7,7> (uint64_t target, uint64_t pattern, uint64_t mask) { return -1; };

template< int I, int J > inline int
scanright (uint64_t target, uint64_t pattern, uint64_t mask)
{
    return scan< 0 >(target, pattern, mask) == 0 ? I : scanright < I+1, J >(target, pattern >> 8, mask >> 8);
}

// void Executor::single_step_match(uint64_t cc[2]){
//   if( scan<0>(cc[0], 0x0000000000f6314d, 0x0000000000ffffff) >= 0 ) { 
//     Executor::tase_helper_write((uint64_t) &(target_ctx_gregs[GREG_EFL].u64), klee::ConstantExpr::create(0x2, Expr::Int64));
//     target_ctx_gregs[GREG_RIP].u64 += 3; // xor %r14,%r14
//     if( modelDebug ) {
//       std::cout << "Killing Flags (xor)" << std::endl;
//     }
//     ex_state = EXECUTION_STATE::SKIP;
//   } else if ( cc[0] == 0x4566363c751101c4 && scan< 0 >(cc[1], 0x0000850fff17380f, 0x0000ffffffffffff) >= 0 ) { 
//     target_ctx_gregs[GREG_RIP].u64 += 32; // vpcmpeqw/ptest/movq/leaq/jne
//     if( modelDebug ){
//       std::cout << "Skipping eager instrumentation (A)..." << std::endl;
//     }
//     ex_state = EXECUTION_STATE::SKIP;	
//   } else if ( scan< 0 >(cc[0], 0x9e00000000008948, 0xff0000000000ffff) >= 0 ) { 
//     // movq/lahf/movl/shrxq/vpcmpeqw/ptest/movq/leaq/jne/sahf/movq
//     target_ctx_gregs[GREG_RIP].u64 += 53;
	
//     if( modelDebug ){                                                                                       
//       std::cout << "Skipping eager instrumentation (B)..." << std::endl;                                    
//     }
//     ex_state = EXECUTION_STATE::SKIP;	  
//   } else if ( scan< 0 >(cc[0], 0x000000000000009f, 0x00000000000000ff) == 0 ) {
//     // lahf/movl/shrxq/vpcmpeqw/ptest/movq/leaq/jne/sahf
//     target_ctx_gregs[GREG_RIP].u64 += 37;
	
//     if( modelDebug ){                                                                                       
//       std::cout << "Skipping eager instrumentation (C)..." << std::endl;                                    
//     }
//     ex_state = EXECUTION_STATE::SKIP;	  
//   } else if ( scan< 0 >(cc[0], 0x0000000000308d44, 0x00000000000038fff4) == 0 ) {
//     // leaq -> r14
//     // get length: https://wiki.osdev.org/X86-64_Instruction_Encoding#64-bit_addressing
//     //        MOD
//     //  B.RM       0.000-0.011(0-3) 0.100  0.101  0.110-1.011(6-11) 1.100 1.101  1.110-1.111(14-15)
//     //         00        3           SIB      7         3             SIB     7        3
//     //         01        4           SIB      4         4             SIB     4        4
//     //         10        7           SIB      7         7             SIB     7        7
//     // SIB -> check base. If mod == 00 and base is 0.101 or 1.101 then size = 8, o.w. size = 4. If mod == 10, size = 8. If mod == 01, size = 5.
	
//     auto brm = ((0x00000000000001 & cc[0]) << 3) | ((0x0000000000070000 & cc[0]) >> 16);
//     auto mod = (0x0000000000c00000 & cc[0]) >> 22;
//     auto size = 0;
	
//     if ( brm == 4 || brm == 12 ) {
//       auto base = (0x00000007000000 & cc[0]) >> 6*4;
//       size = mod == 0 ? ( base == 5 ? 8 : 4 ) : ( mod == 2 ? 8 : 5 );
//     } else if ( brm == 5 || brm == 13 ) {
//       size = mod < 1 ? 7 : mod < 2 ? 4 : 7;
//     } else {
//       size = mod < 1 ? 3 : mod < 2 ? 4 : 7;
//     }

//     uint64_t c = 0;

//     if ( size < 8 ) {
//       c = (cc[0] >> ((size)*8)) | (cc[1] << ((8-size)*8)); // skip past current instr
//     } else {
//       c = cc[1];
//     }
	
//     // check for potential next instrs, take earliest appearance
//     auto shr = scanleft< 0, 7 >(c, 0x0000000000eed149, 0x0000000000ffffff); // shrq ( eflags dead and rax dead )
//     auto mov = scanleft< 0, 7 >(c, 0x0000000000008948, 0x000000000000ffff); // movq ( eflags live and rax live )
//     auto lah = scanleft< 0, 7 >(c, 0x000000000000009f, 0x00000000000000ff); // lahf ( eflags live only )
//     shr = shr >= 0 ? shr : 8;
//     mov = mov >= 0 ? mov : 8;
//     lah = lah >= 0 ? lah : 8;

//     auto update = shr < mov ? ( shr < lah ? 35 : 37 ) : ( mov < lah ? 51 : 37 );
//     target_ctx_gregs[GREG_RIP].u64 += size + update ;

//     if ( modelDebug ) {
//       std::cout << "Skipping eager instrumentation (D[" << size+update << "][" << shr << "][" << mov << "][" << lah << "])... " << std::hex << c << std::endl;
//     }
//     ex_state = EXECUTION_STATE::SKIP;	  
//   } else {
//     ex_state = EXECUTION_STATE::INTERP;
//   }
// }

// this should match what's in LLVM
unsigned regmap[12] = {GREG_RAX, GREG_RBX, GREG_RCX, GREG_RDX, GREG_RSI, GREG_RDI, GREG_R8, GREG_R9, GREG_R10, GREG_R11, GREG_R12, GREG_R13};


// prev_rip is the cartridge_rip, which should be the cartridge head location for the  prev cartridge
// after interpreting the next RIP value should be the head of the next cartridge
/*
void Executor::killDeadRegs( uint64_t prev_rip ) {
  auto it = cartridge_regstatus.find( prev_rip );  
  if( it == cartridge_regstatus.end() )
    return;

  //  auto next = cartridge_regstatus.find( target_ctx_gregs[GREG_RIP].u64 );
  for( auto i = 0; i < 12; i++ ) {
    // it's in the kill list (it->first) for the prev MBB // and the new MBB doesn't have it in live_ins (next->second)
    uint64_t *buf = &target_ctx_gregs[regmap[i]].u64;
    if( tase_buf_has_taint(buf, sizeof(uint64_t)) && (it->second.first & (1<<i)) != 0 ) { // && (next->second.second & (1<<i)) == 0 ) {
      LOG_TASE("Killing Register %d at end of cartridge at %lx, going to cartridge at %lx\n", i, prev_rip, target_ctx_gregs[GREG_RIP].u64);
      tase_helper_write((uint64_t) buf, klee::ConstantExpr::create(0, Expr::Int64));
    }
  }
  }*/

// prev_rip is the cartridge_rip, which should be the cartridge head location for the  prev cartridge
// after interpreting the next RIP value should be the head of the next cartridge
/* void Executor::killDeadRegs( uint64_t prev_rip ) {
  auto it = cartridge_regstatus.find( prev_rip );
  if( it == cartridge_regstatus.end() )
    return;

  //  auto next = cartridge_regstatus.find( target_ctx_gregs[GREG_RIP].u64 );
  for( auto i = 0; i < 12; i++ ) {
    // it's in the kill list (it->first) for the prev MBB // and the new MBB doesn't have it in live_ins (next->second)
    uint64_t *buf = &target_ctx_gregs[regmap[i]].u64;
    if( tase_buf_has_taint(buf, sizeof(uint64_t)) && (it->second & (1<<i)) == 0 ) {
      DBG_TASE("Killing Register %d at end of cartridge at %lx, going to cartridge at %lx\n", i, prev_rip, target_ctx_gregs[GREG_RIP].u64);
      tase_helper_write((uint64_t) buf, klee::ConstantExpr::create(0, Expr::Int64));
    }
  }
  }*/

void Executor::killDeadRegs( uint64_t prev_rip ) {
  LOG_TASE("Checking regstatus at %lx\n", prev_rip);LOG_FLUSH();
  auto it = cartridge_regstatus.find( prev_rip );
  if( it == cartridge_regstatus.end() )
    return;

  //  auto next = cartridge_regstatus.find( target_ctx_gregs[GREG_RIP].u64 );
  for( auto i = 0; i < 12; i++ ) {

    uint64_t *buf = &target_ctx_gregs[regmap[i]].u64;
    if( tase_buf_has_taint(buf, sizeof(uint64_t)) && (it->second.second & (1<<i)) == 0 ) { // && (next->second.second & (1<<i)) == 0 ) {
      LOG_TASE("Killing Register %d at end of cartridge at %lx, going to cartridge at %lx\n", i, prev_rip, target_ctx_gregs[GREG_RIP].u64);
      tase_helper_write((uint64_t) buf, klee::ConstantExpr::create(0, Expr::Int64));
    }
  }
}

void Executor::fastWipeReg(void * ptr, std::vector<uint8_t> bytes) {
  uint64_t addrBase = (uint64_t) ptr;
  size_t size = bytes.size();
  //Todo -- add check to make sure ptr is contained within buffer mapped to represent registers
  //Sanity checks.  Todo -- make sure to update for larger poison size
  if ((addrBase % 2 == 1) || (size % 2 == 1)) {
    LOG_TASE("fastWipeReg called on odd ptr or odd size.  Exiting \n");LOG_FLUSH();
    worker_error(Running,Stopped);
  }

  //Doing a full lookup to map an address to the corresponding MO/OS can be expensive,
  //so basically just save the result.  
  static bool hasBeenCalled = false;
  static const MemoryObject * regMO; 
  static ObjectState * regOS;
  if (hasBeenCalled == false) {
    hasBeenCalled = true;
    ref<Expr> addrExpr = ConstantExpr::create(addrBase, Expr::Int64);

    //Find a better way to do this.  Using logic from Executor::executeMemoryOperation
    //begin gross------------------
    ObjectPair op;
    bool success;
    if (! GlobalExecutionStatePtr->addressSpace.resolveOne(*GlobalExecutionStatePtr,solver,addrExpr, op, success) ) {
      LOG_TASE("ERROR in fastWipeReg: Couldn't resolve addr to fixed value \n");
      worker_error(Running,Stopped);
    }

    ref<Expr> offset = op.first->getOffsetExpr(addrExpr);
    //end gross----------------------------
    regOS = GlobalExecutionStatePtr->addressSpace.getWriteable(op.first, op.second);
    regMO = op.first;
  }

  //Sanity check for bounds
  uint64_t objStartAddr = regMO->address;
  unsigned objSize = regMO->size;
  uint64_t objEndAddr = objStartAddr + objSize -1;
  if ((addrBase < objStartAddr) || (addrBase > objEndAddr)) {
    LOG_TASE("ERROR: base address not in MO \n");
    worker_error(Running,Stopped);
  }
  if ((addrBase + size) < objStartAddr || (addrBase + size) > objEndAddr) {
    LOG_TASE("ERROR: end of buf not in MO \n");
    worker_error(Running,Stopped);
  }
  //Actually do the update.  
  unsigned objOffset = (unsigned) (addrBase - objStartAddr);
  for (int i = 0; i < size; i++) {
    //If the byte is flushed for some reason, we need to update this fn to handle symbolic offsets
    if (regOS->isByteFlushed(objOffset + i) ) {
      LOG_TASE("ERROR: Handle symbolic offsets in fastWipeReg \n");
      worker_error(Running,Stopped);
    }    
    regOS->write8(objOffset + i, bytes[i]);
    //No need to apply any psn since we're already assuming alignment
  }

}

//Speculatively try to make registers concrete if a solution exists
int IVCRefreshTime = 0;
double IVCTime = 0;

void Executor::impliedValueConcRegs() {
  double T0 = util::getWallTime();
  static int RBXCtr = 0;
  static int RAXCtr = 0;
  static int RDXCtr = 0;
  static int RBPCtr = 0;
  LOG_TASE("Entering impliedValueConcRegs! \n");LOG_FLUSH();
  LOG_TASE("DBG 1 \n");LOG_FLUSH();
  ref<Expr> RBXExpr = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_RBX].u64, 8);
  LOG_TASE("DBG 2 \n");LOG_FLUSH();
  //if (RBXCtr % IVCRefreshTime == 0) {
  RBXCtr++;
  if (!(isa<ConstantExpr>(RBXExpr))) {
    LOG_TASE("Trying to call getnposs \n");LOG_FLUSH();
    std::vector<ref<Expr>> Vals = getNPossibleValues(*GlobalExecutionStatePtr, RBXExpr, 3, false);
    LOG_TASE("IVC: RBX has at least %d vals \n", Vals.size());
    if (Vals.size() == 1) {
      LOG_TASE("Opportunity to concretize RBX! \n");LOG_FLUSH();
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RBX].u64, Vals[0]);
    }
  }
  //}
  LOG_TASE("DBG 3 \n");LOG_FLUSH();
  ref<Expr> RAXExpr = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_RAX].u64, 8);
  //if (RAXCtr % IVCRefreshTime == 0) {
  RAXCtr++;
  if (!(isa<ConstantExpr>(RAXExpr))){
    LOG_TASE("Trying to call getnposs \n");LOG_FLUSH();
    std::vector<ref<Expr>> Vals = getNPossibleValues(*GlobalExecutionStatePtr, RAXExpr, 3, false);
    LOG_TASE("IVC: RAX has at least %d vals \n", Vals.size());
    if (Vals.size() == 1) {
      LOG_TASE("Opportunity to concretize RAX! \n");LOG_FLUSH();
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX].u64, Vals[0]);
    }
  }
  //}

  ref<Expr> RDXExpr = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_RDX].u64, 8);
  //if (RDXCtr % IVCRefreshTime == 0) {
  RDXCtr++;
  if (!(isa<ConstantExpr>(RDXExpr))) {
    LOG_TASE("Trying to call getnposs \n");LOG_FLUSH();
    std::vector<ref<Expr>> Vals = getNPossibleValues(*GlobalExecutionStatePtr, RDXExpr, 3, false);
    LOG_TASE("IVC: RDX has at least %d vals \n", Vals.size());
    if (Vals.size() == 1) {
      LOG_TASE("Opportunity to concretize RDX! \n");LOG_FLUSH();
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDX].u64, Vals[0]);
    }
   
  }

  ref<Expr> RBPExpr = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_RBP].u64, 8);
  //if (RBPCtr % IVCRefreshTime == 0) {
  RBPCtr++;
  if (!(isa<ConstantExpr>(RBPExpr))) {
    LOG_TASE("Trying to call getnposs \n");LOG_FLUSH();
    std::vector<ref<Expr>> Vals = getNPossibleValues(*GlobalExecutionStatePtr, RBPExpr, 3, false);
    LOG_TASE("IVC: RBP has at least %d vals \n", Vals.size());
    if (Vals.size() == 1) {
      LOG_TASE("Opportunity to concretize RBP! \n");LOG_FLUSH();
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RBP].u64, Vals[0]);
    }
  }
  
  
  //}
  IVCTime += util::getWallTime() - T0;
  LOG_TASE("Time in IVC: %lf \n", IVCTime);LOG_FLUSH();
}

//Get rid of "garbage" beyond the edge of the stack to avoid encountering old dead EXPRs.
void Executor::calleeWipePastStack() {
  //Disabled for BFS to make training run faster
  /*
  if (!(explorationType ==TASEExplorationType::BFS) ) {
    LOG_TASE("Calling calleeWipePastStack \n");LOG_FLUSH();
    double t0 = util::getWallTime();
    uint64_t * currSP =(uint64_t *) target_ctx_gregs[GREG_RSP].u64; //What if it's not aligned?
    uint64_t origSP = (uint64_t) currSP;
    currSP--; //Stack "grows" downwards
    for (int i = 0; i < 10000; i++) {
      currSP--;
      //LOG_TASE("CurrSP is 0x%lx \n", (uint64_t) currSP);
      tase_helper_write((uint64_t) (currSP), klee::ConstantExpr::create(0, Expr::Int64));
    }
    LOG_TASE("Wiping took %lf seconds down from addr 0x%lx to 0x%lx \n", util::getWallTime()- t0, origSP, (uint64_t) currSP);LOG_FLUSH();
  }
  */
}

void Executor::calleeKillDeadRegs() {
  LOG_TASE("Calling calleekilldeadregs \n");LOG_FLUSH();
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R8].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R9].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R10].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R11].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RCX].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDX].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDI].u64, klee::ConstantExpr::create(0, Expr::Int64));
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RSI].u64, klee::ConstantExpr::create(0, Expr::Int64));
  calleeWipePastStack();
}

uint64_t pre_interp_RIP;
FILE * tetrinet_field_log;
extern void draw_tetrinet_field(FILE *f);
void Executor::klee_interp_internal() {
  run_interp_traps++;
  double model_start_time;

  while (true) {
    double dbgTime1 = util::getWallTime();
    run_interp_insts++;
    interpCtr++;
    if (tetrinet_field_log == NULL) {
      tetrinet_field_log = fopen("fieldLog", "w+");
    }
    draw_tetrinet_field(tetrinet_field_log);
    
    uint64_t rip = target_ctx_gregs[GREG_RIP].u64;
    uint64_t rip_init = rip;


    auto mod = fnModelMap.find(cartridge_rip) != fnModelMap.end() ? fnModelMap.find(cartridge_rip) : fnModelMap.find(rip);
    void (klee::Executor::*fp)() = mod == fnModelMap.end() ? NULL : mod->second;
    
    if ( taseDebug > 1 ) { // MOD_TASE, but since we tested just use LOG_TASE to skip the checks
      printDebugInterpHeader();       
      LOG_TASE("RIP at top of klee_interp_internal loop is %lx\n", rip);
      if( localStack ) {
	LOG_TASE("local stack: \n");
	for( int x = -2; x < localStack; x++ ) {
	  if( x == 0 ) {
	    LOG_TASE("\t-->[ %.16lx ]", *((uint64_t*)target_ctx_gregs[GREG_RSP].u64));
	  } else {
	    if(  *((uint64_t*)(target_ctx_gregs[GREG_RSP].u64 + 8*x)) == 0x1badf00d4dadb0d1 ) {
	      LOG_TASE("\t---[ %.16lx ]---\n", *((uint64_t*)(target_ctx_gregs[GREG_RSP].u64 + 8*x)));
	      break;
	    }
	    LOG_TASE("\t   [ %.16lx ]", *((uint64_t*)(target_ctx_gregs[GREG_RSP].u64 + 8*x)));
	  }
	  if( target_ctx_gregs[GREG_RSP].u64 + 8*x == target_ctx_gregs[GREG_RBP].u64 ) {
	    LOG_TASE("<-rbp-");
	  }
	  LOG_TASE("\n");
	}

      } else {
        LOG_TASE("Top of stack: 0x%lx\n", *(uint64_t*)target_ctx_gregs[GREG_RSP].u64);
      }
      LOG_TASE("interp_state: %s\n", ex_state.print_istate().c_str());
      LOG_TASE("Model found at 0x%lx or 0x%lx: %s\n", cartridge_rip, rip, mod == fnModelMap.end() ? "false" : "true");
    }

       // in the case we advance within the while loop to a model
    if( ex_state != EXECUTION_STATE::MODEL && ex_state != EXECUTION_STATE::PROHIB && mod != fnModelMap.end() ){
      MOD_TASE("Updating interp_state to %s\n", ex_state.print_istate().c_str());
      ex_state = EXECUTION_STATE::MODEL;
    }

    uint64_t cc = *(uint64_t*)target_ctx_gregs[GREG_RIP].u64;
    DBG_TASE("next instr bytes: %lx\nrsp global: %lx and real rsp: %lx\n", cc, rsp_global, target_ctx_gregs[GREG_RSP].u64);
      
    if( scan< 0 >(cc, 0x00000000000258948, 0x0000000000ffffff) >= 0 ) {
      DBG_TASE("Instruction to mov rsp val, rsp should be changing:: %lx and real rsp val:: %lx\n", rsp_global, *(uint64_t*)target_ctx_gregs[GREG_RSP].u64);
    }

    
    //LOG_FLUSH();
    
    switch( ex_state.istate ) {
    case EXECUTION_STATE::PROHIB_RESUME:
      if ( ex_state.is_concrete() && tran_max == 0 && target_ctx_gregs[GREG_RIP].u64 == init_trap_RIP ) {
	DBG_TASE("Repeated faults detected for prohib function\n");
	ex_state = EXECUTION_STATE::PROHIB_FAULT;
      }
    case EXECUTION_STATE::RESUME:
      DBG_TASE("Attempting to return to native execution \n");
      return;

    case EXECUTION_STATE::MODEL:
      if( measureTime )
	model_start_time = util::getWallTime();
      
      if( fp == NULL ) {

	LOG_TASE("Cannot run model, not found\n");
	worker_error(Stopped, Running);
	exit(1);
      }
      
      (this->*fp)();
      cartridge_rip = 0; // so we don't reenter the model on resume
      
      if( measureTime )
	run_model_time = util::getWallTime() - model_start_time;
      
      ex_state = ex_state.is_mixedMode() ? EXECUTION_STATE::RESUME : EXECUTION_STATE::INTERP;//Registers could

      //(and do)  sometimes have taint after a modeled fn. this case is handled in the ex_state.update() call at the end of the loop.
      break;
 
    case EXECUTION_STATE::BOUNCEBACK:
      assert(false && "BOUNCEBACK state found in klee_interp_internal!");
      break;

    case EXECUTION_STATE::SKIP:
    case EXECUTION_STATE::FAULT:
    case EXECUTION_STATE::PROHIB_FAULT:
    case EXECUTION_STATE::PROHIB:
    case EXECUTION_STATE::INTERP:

      DBG_TASE("Checking for skippable instrs\n");
      DBG_TASE("interp_state dbg 1.1: %s\n", ex_state.print_istate().c_str()); LOG_FLUSH();
      if( scan< 0 >(cc, 0x00000000003d8d4c, 0x0000000000ffffff) >= 0 ) {
	// convert first four bytes of cc to uint32_t
	uint32_t offset = 0;
	for( int i = 0; i < 4; i++ ) {
	  offset |= (cc & (0xff000000 << (8*i))) >> (3*8);
	}
	
	cartridge_rip = target_ctx_gregs[GREG_RIP].u64;
	target_ctx_gregs[GREG_RIP].u64 += 7 + offset;

	saved_rax = ( ( cc & 0xff00000000000000 ) == 0x9c00000000000000 ? 1 : 0 ); 
	
	MOD_TASE("Found \"leaq 0x%x(%%rip),%%r15 instruction, skipping to 0x%lx\n", offset, target_ctx_gregs[GREG_RIP].u64);
	ex_state = EXECUTION_STATE::SKIP;
	break;
      }

      if( scan<0>(cc, 0x0000000000f6314d, 0x0000000000ffffff) >= 0 ) { 
	Executor::tase_helper_write((uint64_t) &(target_ctx_gregs[GREG_EFL].u64), klee::ConstantExpr::create(0x2, Expr::Int64));
	target_ctx_gregs[GREG_RIP].u64 += 3; // xor %r14,%r14
	MOD_TASE("Killing Flags\n");
	ex_state = EXECUTION_STATE::SKIP;
	break;
      }

      
      
      pre_interp_RIP = target_ctx_gregs[GREG_RIP].u64;
      if (pre_interp_RIP == 0x5b3cbe) {
	LOG_TASE("We appear to be entering mavlink_finalize_msg \n");LOG_FLUSH();
	/*
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R8].u64, klee::ConstantExpr::create(0, Expr::Int64));
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R9].u64, klee::ConstantExpr::create(0, Expr::Int64));
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R10].u64, klee::ConstantExpr::create(0, Expr::Int64));
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R11].u64, klee::ConstantExpr::create(0, Expr::Int64));
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R12].u64, klee::ConstantExpr::create(0, Expr::Int64));
	*/
      }
      LOG_TASE("pre_interp_rip: 0x%lx \n", pre_interp_RIP);LOG_FLUSH();
      if (pre_interp_RIP == 0x5b4096) {
	LOG_TASE("Special DBG \n");LOG_FLUSH();
	ref<Expr> R12Expr = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_R12].u64, 8);
	ref<Expr> RBXExpr = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_RBX].u64, 8);
	std::vector<ref<Expr>> R12Vals = getNPossibleValues(*GlobalExecutionStatePtr, R12Expr, 10, false);
	std::vector<ref<Expr>> RBXVals = getNPossibleValues(*GlobalExecutionStatePtr, RBXExpr, 10, false);
	LOG_TASE("Found %d vals for r12 and %d for rbx \n", R12Vals.size(), RBXVals.size() ); LOG_FLUSH();
	if (R12Vals.size() == 1) {
	  LOG_TASE("Concretizing R12 \n");LOG_FLUSH();
	  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R12].u64, R12Vals[0]);
	}
	if (RBXVals.size() == 1) {
	  LOG_TASE("Concretizing RBX \n");LOG_FLUSH();
	  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RBX].u64, RBXVals[0]);
	}
      }
      
      coreInterpStartTime = util::getWallTime();
      LOG_TASE("%lf seconds in dbg1 \n", util::getWallTime() - dbgTime1);
      LOG_TASE("%lf seconds since eval started at runcoreinterp\n", util::getWallTime() - postInitStartTime);
      runCoreInterpreter(target_ctx_gregs);
      LOG_TASE("spent %lf seconds in core interp coreinterpdbg \n", util::getWallTime() - coreInterpStartTime);
      double dbg2 = util::getWallTime();
      tryKillFlags( cartridge_rip ); 
      killDeadRegs( cartridge_rip ); // rip var not updated until next cycle
      if (TASEIVC) {
	impliedValueConcRegs();
      }
      ex_state = EXECUTION_STATE::INTERP;
      LOG_TASE("%lf seconds in dbg2 \n", util::getWallTime() - dbg2);
      break;
    } // end of switch
    if( taseDebug > 0 ) {
      LOG_FLUSH();
    }

    // fast check here is a subset of is_concrete's check and it's run already
    if( ex_state.is_concrete() || tase_buf_has_taint((void *) &(target_ctx_gregs[GREG_RIP].u64), 8) ) { // fast check for potential taint
      ref<Expr> RIPExpr = tase_helper_read((uint64_t) &(target_ctx_gregs[GREG_RIP].u64), 8); // full/slow check
      if (!(isa<ConstantExpr>(RIPExpr))) {
	LOG_TASE("Forking on possible RIP values in klee_interp_internal\n");
	double ripForkTime = util::getWallTime() ;
	forkOnPossibleRIPValues(RIPExpr, rip_init);
	LOG_TASE("Spent %lf seconds on forkOnPossibleRIPValues \n", util::getWallTime() - ripForkTime);
        if ( taseDebug ) {
          ref<Expr> FinalRIPExpr = target_ctx_gregs_OS->read(GREG_RIP * 8, Expr::Int64);
          if ( !(isa<ConstantExpr>(FinalRIPExpr)) ) {
	    LOG_TASE("ERROR: Failed to concretize RIP \n");LOG_FLUSH();
	    worker_error(Stopped, Running);
            std::exit(EXIT_FAILURE);
          }
        }
      }
    }

    ex_state.update();
  } // end while
  

  static int numReturns = 0;
  numReturns++;
  LOG_TASE("Returning to native \n");LOG_FLUSH();
  if ( taseDebug > 1 ) {
    LOG_TASE("Returning to native execution for time %d\nPrior to return to native execution, ctx is ...\n", numReturns);
    printCtx();
    LOG_TASE("--------RETURNING TO TARGET ---------------\n");
  }
  
  return;
}


void Executor::tryKillFlags(uint64_t rip) {
  //  uint64_t rip = target_ctx_gregs[GREG_RIP].u64;
  if ( ex_state.is_txn_start() && kill_flags.find(rip) != kill_flags.end() ) {
    DBG_TASE("Killing flags (tkf)\n");
    uint64_t zeroFlags = 0x2; // reserved flag bit 1 is always set
    ref<ConstantExpr> zeroExpr = ConstantExpr::create(zeroFlags, Expr::Int64);
    tase_helper_write((uint64_t) &target_ctx_gregs[GREG_EFL], zeroExpr);
  }
}


void Executor::runCoreInterpreter(tase_greg_t * gregs) {
  run_bb_count++;
  double T0;

  DBG_TASE("Entering Core Interpreter at 0x%lx\n", target_ctx_gregs[GREG_RIP].u64)

  if (measureTime) {
    T0 = util::getWallTime();
  }
  KFunction * interpFn = findInterpFunction (gregs, kmodule);
  
  //We have to manually push a frame on for the function we'll be
  //interpreting through.  At this point, no other frames should exist
  // on klee's interpretation "stack".

  GlobalExecutionStatePtr->pushFrameTASE(0,interpFn);

  GlobalExecutionStatePtr->pc = interpFn->instructions;
  GlobalExecutionStatePtr->prevPC = GlobalExecutionStatePtr->pc;
  
  //getArgumentCell(GlobalExecutionStatePtr,interpFn,0).value = arguments[0];
  (GlobalExecutionStatePtr->stack.back().locals[interpFn->getArgRegister(0)]).value = arguments[0];
  if (measureTime) {
    run_tmp_1_time += (util::getWallTime() - T0);
  }
  //bindArgument(interpFn, 0, *GlobalExecutionStatePtr, arguments[0]);

  
  run(*GlobalExecutionStatePtr);
  
  if (measureTime) {
    run_core_interp_time += (util::getWallTime() - T0);
  }
  
}


//This struct is to help the solver for basic blocks with only
//two possible successors (e.g., blocks ending in "jb", "je", etc).

typedef struct cartridgeDestHint {
  uint64_t blockTop;
  uint64_t dest1;
  uint64_t dest2;
} cartridgeSuccessorInfo;

extern std::map<uint64_t, cartridgeSuccessorInfo> knownCartridgeDests;


//Take an Expr and find all the possible concrete solutions.
//Hopefully there's a better builtin function in klee that we can
//use, but if not this should do the trick.  Intended to be used
//to help us get all possible concrete values of RIP (has dependency on RIP).


void Executor::forkOnPossibleRIPValues(ref <Expr> inputExpr, uint64_t initRIP) {
  double t_start = util::getWallTime();

  if (clientName == "TETRINET") {
    forkOnPossibleRIPValuesTetriNET(inputExpr, initRIP);
    LOG_TASE("spent %lf seconds on forkOnPossibleRIPValues \n", util::getWallTime() - t_start);
    return;
  } else if (clientName == "MAVLINK") {
    
    
    forkOnPossibleRIPValuesMavlink(inputExpr, initRIP);
    LOG_TASE("spent %lf seconds on forkOnPossibleRIPValues \n", util::getWallTime() - t_start);
    return;
  } else {
    LOG_TASE("ERROR: clientName not specified \n");
    LOG_TASE("ERROR: Merge in generic fork case for forkOnPossibleRIPValues \n");
    LOG_FLUSH();
    exit(0);
    
  }
  //Fast Path -- Only two possible destinations when exiting basic block;
  std::map<uint64_t, cartridgeSuccessorInfo>::iterator it;
 
  it = knownCartridgeDests.find(initRIP);
  if (it != knownCartridgeDests.end()) {

    uint64_t d1 = it->second.dest1;
    uint64_t d2 = it->second.dest2;

    Solver::Validity rtmp;
    bool s = false;

    double t0 = util::getWallTime();
    s = solver->evaluate(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, ConstantExpr::create(d1, Expr::Int64)), rtmp);
    
    if (!s) {
      LOG_TASE("FATAL ERROR: Solver evaluate call failed in forkOnPossibleRIPValues! \n")
      worker_error(Stopped, Running);
      exit(1);
    }

    double t1 = util::getWallTime();

    DBG_TASE("Solver (forking) calls took %lf seconds in knownCartDests case \n", t1-t0)
    run_solver_time += (t1-t0);
        
    if (rtmp == Solver::True) {
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], ConstantExpr::create(d1,Expr::Int64));
      return;
    } else if (rtmp == Solver::False) {
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], ConstantExpr::create(d2,Expr::Int64));
      return;
    } else {
      LOG_TASE("Prior to fork, time since start is %lf \n", util::getWallTime() - target_start_time)
      //      int isTrueChild = tase_fork(getpid(), initRIP); //Returns 0 for false branch, 1 for true.  Not intuitive
      int isTrueChild = worker_fork(Stopped, Running);
      if (isTrueChild != 0) {
	addConstraint(*GlobalExecutionStatePtr,  EqExpr::create(inputExpr, ConstantExpr::create(d1, Expr::Int64)));
	tase_helper_write( (uint64_t) &target_ctx_gregs[GREG_RIP], ConstantExpr::create(d1,Expr::Int64));
	return;	
      } else {
	addConstraint(*GlobalExecutionStatePtr,  EqExpr::create(inputExpr, ConstantExpr::create(d2, Expr::Int64)));
	tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], ConstantExpr::create(d2,Expr::Int64));
	return;	
      } 
    }
  } else {
    
    solver_start_time = util::getWallTime();
    
    ref <Expr> uniqueRIPExpr  = toUnique(*GlobalExecutionStatePtr,inputExpr);
    solver_end_time = util::getWallTime();
    solver_diff_time = solver_end_time - solver_start_time;

    LOG_TASE("Elapsed solver time (RIP toUnique) is %lf at interpCtr %lu \n", solver_diff_time, interpCtr)
    run_solver_time += solver_diff_time;
  
    if (isa<ConstantExpr> (uniqueRIPExpr)) {
      LOG_TASE("Only one valid value for RIP \n")
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RIP], uniqueRIPExpr);
      return;
    
    } else {

      int maxSolutions = 2; //Completely arbitrary.  Should not be more than 2 for our use cases in TASE
      //or we're in trouble anyway.
    
      int numSolutions = 0;  
      while (true) {
	ref<ConstantExpr> solution;
	numSolutions++;
      
	if (numSolutions > maxSolutions) {
	  LOG_TASE("IMPORTANT: control debug: Found too many symbolic values for next instruction after 0x%lx \n ", initRIP)
	  worker_error(Stopped, Running);
	  exit(1);
	}
      
	solver_start_time = util::getWallTime();
      
	bool success = solver->getValue(*GlobalExecutionStatePtr, inputExpr, solution);
	solver_end_time = util::getWallTime();
      
	solver_diff_time = solver_end_time - solver_start_time;
        LOG_TASE("Elapsed solver time (forking) is %lf at interpCtr %lu \n", solver_diff_time, interpCtr)
	run_solver_time += solver_diff_time;
      
	if (!success) {
	  LOG_TASE("ERROR: couldn't get initial value in forkOnPossibleRIPValues \n")
	  worker_error(Stopped, Running);
	  exit(1);
	}
      
	//	int isTrueChild = tase_fork(getpid(), initRIP); //Returns 0 for false branch, 1 for true.  Not intuitive
	int isTrueChild = worker_fork(Stopped, Running);

	//ABH: Todo -- roll this back and support > 2 symbolic dests for things like indirect jumps
	if (isTrueChild == 0) { //Rule out latest solution and see if more exist
	  ref<Expr> notEqualsSolution = NotExpr::create(EqExpr::create(inputExpr,solution));
	  if (klee::ConstantExpr *CE = dyn_cast<klee::ConstantExpr>(notEqualsSolution)) {
	    if (CE->isFalse()) {
	      LOG_TASE("IMPORTANT: forked child %d is not exploring a feasible path \n", getpid())
	      worker_error(Stopped, Running);
	      exit(1);
	    }
	  }
	
	
	  addConstraint(*GlobalExecutionStatePtr, notEqualsSolution);

	  solver_start_time = util::getWallTime();
	  success = solver->getValue(*GlobalExecutionStatePtr, inputExpr, solution);
	  solver_end_time = util::getWallTime();
    
	  solver_diff_time = solver_end_time - solver_start_time;
	  run_solver_time += solver_diff_time;

	  LOG_TASE("Elapsed solver time (fork - path constraint) is %lf at interpCtr %lu \n", solver_diff_time, interpCtr)
      
	  if (!success) {
	    LOG_TASE("ERROR: couldn't get RIP value in forkOnPossibleRIPValues for false child \n")
	    worker_error(Stopped, Running);
	    exit(1);
	  }

	  LOG_TASE("IMPORTANT: control debug: Found dest RIP 0x%lx on false branch in forkOnRip from RIP 0x%lx with pid %d \n", (uint64_t) solution-\
>getZExtValue(), initRIP, getpid())
	  addConstraint(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, solution));
	  target_ctx_gregs_OS->write(GREG_RIP*8, solution);
	  break;

	} else { // Take the concrete value of solution and explore that path.
	  LOG_TASE("IMPORTANT: control debug: Found dest RIP 0x%lx on true branch in forkOnRip from RIP 0x%lx with pid %d \n", (uint64_t) solution->\
getZExtValue(), initRIP, getpid())
	  addConstraint(*GlobalExecutionStatePtr, EqExpr::create(inputExpr, solution));
	  target_ctx_gregs_OS->write(GREG_RIP*8, solution);
	  break;
	}
      }
    }
  }
}

int Executor::forkOnPossibleIRBranches( ref<Expr> condition, std::vector<std::vector<float>> IR_Constraint_BOWs) {
  double t_start = util::getWallTime();
  int res = -1;
  if (clientName == "TETRINET") {
    res = forkOnPossibleIRBranchesTetriNET(condition, IR_Constraint_BOWs);
    LOG_TASE("spent %lf seconds on forkOnPossibleIRBranches \n", util::getWallTime() - t_start);LOG_FLUSH(); 
  } else if (clientName == "MAVLINK") {
    res = forkOnPossibleIRBranchesMavlink(condition, IR_Constraint_BOWs);
    LOG_TASE("spent %lf seconds on forkOnPossibleIRBranches \n", util::getWallTime() - t_start);LOG_FLUSH();
  } else {
    LOG_TASE("ERROR: clientName not specified \n");
    LOG_TASE("ERROR: Merge in generic fork case for forkOnPossibleIRBranches \n");LOG_FLUSH();
    exit(0);
  }
  if(res == -1) {
    LOG_TASE("ERROR in forkOnPossibleIRBranches \n");LOG_FLUSH();
    exit(0);
  }

  return res;
}

void Executor::printCtxExpr() {
  LOG_TASE("R8  : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R8].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R9  : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R9].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R10 : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R10].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R11 : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R11].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R12 : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R12].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R13 : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R13].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R14 : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R14].u64, 8)->dumpToStr().c_str());
  LOG_TASE("R15 : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_R15].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RDI : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RDI].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RSI : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RSI].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RBP : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RBP].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RBX : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RBX].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RDX : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RDX].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RAX : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RAX].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RCX : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RCX].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RSP : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RSP].u64, 8)->dumpToStr().c_str());
  LOG_TASE("RIP : %s\n", tase_helper_read((uint64_t)&target_ctx_gregs[GREG_RIP].u64, 8)->dumpToStr().c_str());
}

void Executor::printCtx() {
  LOG_TASE("R8   : 0x%lx \n", target_ctx_gregs[GREG_R8].u64)
    LOG_TASE("R9   : 0x%lx \n", target_ctx_gregs[GREG_R9].u64)
    LOG_TASE("R10  : 0x%lx \n", target_ctx_gregs[GREG_R10].u64)
    LOG_TASE("R11  : 0x%lx \n", target_ctx_gregs[GREG_R11].u64)
    LOG_TASE("R12  : 0x%lx \n", target_ctx_gregs[GREG_R12].u64)
    LOG_TASE("R13  : 0x%lx \n", target_ctx_gregs[GREG_R13].u64)
    LOG_TASE("R14  : 0x%lx \n", target_ctx_gregs[GREG_R14].u64)
    LOG_TASE("R15  : 0x%lx \n", target_ctx_gregs[GREG_R15].u64)
    LOG_TASE("RDI  : 0x%lx \n", target_ctx_gregs[GREG_RDI].u64)
    LOG_TASE("RSI  : 0x%lx \n", target_ctx_gregs[GREG_RSI].u64)
    LOG_TASE("RBP  : 0x%lx \n", target_ctx_gregs[GREG_RBP].u64)
    LOG_TASE("RBX  : 0x%lx \n", target_ctx_gregs[GREG_RBX].u64)
    LOG_TASE("RDX  : 0x%lx \n", target_ctx_gregs[GREG_RDX].u64)
    LOG_TASE("RAX  : 0x%lx \n", target_ctx_gregs[GREG_RAX].u64)
    LOG_TASE("RCX  : 0x%lx \n", target_ctx_gregs[GREG_RCX].u64)
    LOG_TASE("RSP  : 0x%lx \n", target_ctx_gregs[GREG_RSP].u64)
    LOG_TASE("RIP  : 0x%lx \n", target_ctx_gregs[GREG_RIP].u64)


    
    
  // these are w/ bytes reversed from felixcloutier lahf-> AH := RFLAGS(SF:ZF:0:AF:0:PF:1:CF)
  auto x = *(reinterpret_cast<uint16_t*>(&target_ctx_gregs[GREG_EFL].u64));
  LOG_TASE("EFL  : %.04x [ ", x)
  if( x & 0x0001 )
    LOG_TASE("CF ")

  if( x & 0x0004 )
    LOG_TASE("PF ")

  if( x & 0x0010 )
    LOG_TASE("AF ")
  
  if( x & 0x0040 )
    LOG_TASE("ZF ")

  if( x & 0x0080 )
    LOG_TASE("SF ")

  if( x & 0x0800 )
    LOG_TASE("OF ")

  LOG_TASE("] ( ")  // extras

  if( x & 0x0002 )
    LOG_TASE("RB ") // should always be set

  if( x & 0x0008 )
    LOG_TASE("RB2 ") // should never be set

  if( x & 0x0020 )
    LOG_TASE("RB3 ") // should never be set
  
  if( x & 0x0100 )
    LOG_TASE("TF ")  // trap flag
  
  if( x & 0x0200 )
    LOG_TASE("IF ") // interrupt flag

  if( x & 0x0400 )
    LOG_TASE("DF ") // direction flag (string ops)

  if( x & 0x8000 )
    LOG_TASE("MD ") // reserved Mode flag, should never be set

  LOG_TASE(")")
  
  if( saved_rax != 0 )
    LOG_TASE(" live")

  LOG_TASE("\n")

      printCtxExpr();
  
  return;
}


void Executor::initializeInterpretationStructures (Function *f) {
  ufmanager = new UFManager();
  ufmanager_cheat = new UFManager();//Additional union find manager for
  //all constraints in ufmanager PLUS extra constraints to represent concrete keystrokes
  //when training path selection in TASE
  
  LOG_TASE("INITIALIZING INTERPRETATION STRUCTURES \n");
  loadGetNPossibleValuesCache(); //Todo -- gate this so it's an option for testing.
  
  GlobalExecutorPtr = this;
  GlobalExecutionStatePtr = new ExecutionState(kmodule->functionMap[f]);

  uint64_t regAddr = (uint64_t) target_ctx_gregs;
  ref<ConstantExpr> regExpr = ConstantExpr::create(regAddr, Context::get().getPointerWidth());  
  arguments.push_back(regExpr);
  
  initializeGlobals(*GlobalExecutionStatePtr);
  //Set up the KLEE memory object for the stack, and back the concrete store with the actual stack.
  //Need to be careful here.  The buffer we allocate for the stack is char [X] target_stack. It
  // starts at address StackBase and covers up to StackBase + sizeof(target_stack) -1.

  
  uint64_t stackBase = (uint64_t) &target_ctx.target_stack;
  uint64_t stackSize = STACK_SIZE;
  tase_map_buf((uint64_t) stackBase, stackSize, "stack");
  LOG_TASE("Stack: %lx to %lx\n", stackBase, (stackBase + stackSize + 1))
  
  target_ctx_gregs_MO = addExternalObject(*GlobalExecutionStatePtr, (void *) target_ctx_gregs, TASE_NGREG * TASE_GREG_SIZE, false );
  const ObjectState *targetCtxOS = GlobalExecutionStatePtr->addressSpace.findObject(target_ctx_gregs_MO);
  target_ctx_gregs_OS = GlobalExecutionStatePtr->addressSpace.getWriteable(target_ctx_gregs_MO,targetCtxOS);
  target_ctx_gregs_OS->concreteStore = (uint8_t *) target_ctx_gregs;

  /*target_ctx_xmms_MO = addExternalObject(*GlobalExecutionStatePtr, (void*) target_ctx.xmm, 8*XMMREG_SIZE, false);
  const ObjectState *targetCtxXOS = GlobalExecutionStatePtr->addressSpace.findObject(target_ctx_xmm_MO);
  target_ctx_xmms_OS = GlobalExecutionStatePtr->addressSpace.getWritable(target_ctx_xmms_MO, targetCtxXOS);
  target_ctx_xmms_OS->concreteStore = (uint8_t *) target_ctx_xmms;
  */
  //Map in read-only globals
  //Todo -- find a less hacky way of getting the exact size of the .rodata section

  rodata_base_ptr = (void *) (&_IO_stdin_used);
  rodata_size = (uint64_t) ((uint64_t) (&__GNU_EH_FRAME_HDR) - (uint64_t) (&_IO_stdin_used)) ;

  rodata_size += (0x2949c + 0x2949c); //Hack to map in eh_frame_hdr and eh_frame also
  tase_map_buf((uint64_t) rodata_base_ptr, rodata_size, "rodata");


  //Klee lazily initializes the array of Exprs for a buffer.  So force it to do so now
  //by making a byte on the stack symbolic, and wiping it to 0.
  //uint64_t stackBase = (uint64_t) &target_ctx.target_stack;
  //uint64_t stackSize = STACK_SIZE;
  
  LOG_TASE("Stack starts at 0x%lx with size %d \n", (uint64_t) &target_ctx.target_stack, STACK_SIZE);
  uint64_t flipAddr = (uint64_t) &target_ctx.target_stack + STACK_SIZE/2;
  LOG_TASE("flip addr is 0x%lf \n", flipAddr);
  ref<ConstantExpr> zeroExpr = ConstantExpr::create(0, Expr::Int8);
  tase_make_symbolic_internal(flipAddr, 1, "eager Expr array init");
  tase_helper_write(flipAddr, zeroExpr);
  

  
  //Map in special stdin libc symbol
  //tase_map_buf((uint64_t) &stdin, 8);
  
  //Map in special stdout libc symbol
  //tase_map_buf((uint64_t) &stdout, 8);
  //tase_map_buf((uint64_t) stdout, sizeof(FILE));
  //tase_map(stdout);
  //Map in special stderr libc symbol
  //tase_map_buf((uint64_t) &stderr, 8);
  //printf("stream globals: out/err/in  %lx/%lx/%lx", &stdout, &stderr, &stdin);
  //Map in initialized and uninitialized non-read only globals into klee from .vars file.

  //////////////////////////////
  //For whatever reason, mapping each global doesn't always work in all cases.  Sometimes string constants
  //and other random values are mapped in between the globals we expect in the global vars file.
  //So just map the whole thing.
  MOD_TASE("__data_start: 0x%llx \n", (uint64_t) &__data_start);
  MOD_TASE("__bss_start: 0x%llx \n", (uint64_t) &__bss_start);
  MOD_TASE("_end: 0x%llx \n", (uint64_t) &_end );
  
  uint64_t bssHackSize =  stackBase - (uint64_t) &__bss_start;
  printf("Trying to map portion of __bss at 0x%lx with size %lu \n", (uint64_t) &__bss_start, bssHackSize);
  tase_map_buf ( (uint64_t) &__bss_start, bssHackSize, "bssHack");
  
  
  //////////////////////////////
  


  std::string varsFileLocation = "./" + project + ".vars";
  std::ifstream externals(varsFileLocation);
  int cludge512Ctr = 0;
  if(externals){
    std::string line;
    uint64_t addrVal;
    uint64_t sizeVal;
    int lines = 0;
    while(std::getline(externals, line)){
      std::istringstream ss(line);
      ss >> std::hex >> addrVal >> sizeVal;
      if(!ss){
	LOG_TASE("Error reading externals file within initializeInterpretationStructures() at line %d \"%s\"\n", lines, line.c_str())
	LOG_FLUSH()
	worker_error(Stopped, Running);
	exit(1);
      }
      if((uint64_t) addrVal != (uint64_t) &target_ctx_gregs){
        //if((sizeVal %2) == 1){
	/*
        if((sizeVal % 8) != 0){
          sizeVal += 8 - (sizeVal % 8);
          //++sizeVal;
	  sizeVal += 8; //What could possibly go wrong?  We have an issue sometimes with reading over the edge of the buffer.
	  //It seems to come up often for .bss section vars.  Might be cleaner just to map that whole buffer
	  //all at once than go item by item. -ABH 04292024
	  LOG_TASE("rounding up sizeval to even number - %lu \n", sizeVal);
        }
	*/

	if (addrVal >= (uint64_t) &__bss_start && addrVal < (uint64_t) &__bss_start +   bssHackSize) {
	  LOG_TASE("Not mapping bss var 0x%lx with size %lu \n", addrVal, sizeVal);
	} else {
	  tase_map_buf(addrVal, sizeVal, "global");
	  LOG_TASE("Global: %lx size %lu\n", addrVal, sizeVal);
	}
      }
      lines++;
    }
  } else {
    LOG_TASE("Error reading externals file within initializeInterpretationStructures()\n");LOG_FLUSH();
    worker_error(Stopped, Running);
    exit(1);
  }

  //Todo -- De-hackify this environ variable mapping
  char ** environPtr = environ;
  char * envStr = environ[0];
  size_t len = 0;
  char * latestEnvStr = NULL;
  
  while (envStr != NULL) {
    
    uint32_t size = strlen(envStr);
    LOG_TASE("Found env var at 0x%lx with size 0x%x \n", (uint64_t) envStr, size)

    envStr = *(environPtr++);
    if (envStr != NULL) {
      len = strlen(envStr);
      latestEnvStr = envStr;
    }
  }

  uint64_t baseEnvAddr =  (uint64_t) environ[0];
  uint64_t endEnvAddr = (uint64_t) latestEnvStr + len + 1;
  uint64_t envSize = endEnvAddr - baseEnvAddr;

  if (envSize % 2 == 1)
    envSize++;

  tase_map_buf(baseEnvAddr, envSize, "env");
  
  //Add mappings for stderr and stdout
  //Todo -- remove dependency on _edata location
  //printf("Mapping edata at 0x%lx \n", (uint64_t) &edata);
  tase_map_buf((uint64_t) &edata, 16, "edata");

  //Get rid of the dummy function used for initialization
  GlobalExecutionStatePtr->popFrame();
  processTree = new PTree(GlobalExecutionStatePtr);
  GlobalExecutionStatePtr->ptreeNode = processTree->root;
  bindModuleConstants(); //Moved from "run"
  loadFnModelMap();
  
  FILE * stats = fopen("/proc/self/statm", "r");
  if (stats != NULL ) {
    LOG_TASE("Couldn't open statm \n")
  } else {
    LOG_TASE("Opened statm \n")
    uint64_t r1, r2, r3, r4, r5, r6, r7;
    fscanf (stats, "%lu %lu %lu %lu %lu %lu %lu", &r1, &r2, &r3, &r4, &r5, &r6, &r7);
    LOG_TASE("STATM 3:  %lu %lu %lu %lu %lu %lu %lu \n", r1, r2, r3, r4, r5, r6, r7)
    fclose(stats);
  }
}
				   

void Executor::runFunctionAsMain(Function *f,
				 int argc,
				 char **argv,
				 char **envp) {
  std::vector<ref<Expr> > arguments;

  // force deterministic initialization of memory objects
  srand(1);
  srandom(1);
  
  MemoryObject *argvMO = 0;

  // In order to make uclibc happy and be closer to what the system is
  // doing we lay out the environments at the end of the argv array
  // (both are terminated by a null). There is also a final terminating
  // null that uclibc seems to expect, possibly the ELF header?

  int envc;
  for (envc=0; envp[envc]; ++envc) ;

  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  KFunction *kf = kmodule->functionMap[f];
  assert(kf);
  Function::arg_iterator ai = f->arg_begin(), ae = f->arg_end();
  if (ai!=ae) {
    arguments.push_back(ConstantExpr::alloc(argc, Expr::Int32));
    if (++ai!=ae) {
      Instruction *first = &*(f->begin()->begin());
      argvMO =
         memory->allocate((argc + 1 + envc + 1 + 1) * NumPtrBytes,
                           /*isLocal=*/false, /*isGlobal=*/true,
                           /*allocSite=*/first, /*alignment=*/8);

      if (!argvMO)
        klee_error("Could not allocate memory for function arguments");

      arguments.push_back(argvMO->getBaseExpr());

      if (++ai!=ae) {
        uint64_t envp_start = argvMO->address + (argc+1)*NumPtrBytes;
        arguments.push_back(Expr::createPointer(envp_start));

        if (++ai!=ae)
          klee_error("invalid main function (expect 0-3 arguments)");
      }
    }
  }

  ExecutionState *state = new ExecutionState(kmodule->functionMap[f]);
  
  if (pathWriter) 
    state->pathOS = pathWriter->open();
  if (symPathWriter) 
    state->symPathOS = symPathWriter->open();

  if (statsTracker)
    statsTracker->framePushed(*state, 0);

  assert(arguments.size() == f->arg_size() && "wrong number of arguments");
  for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
    bindArgument(kf, i, *state, arguments[i]);

  if (argvMO) {
    ObjectState *argvOS = bindObjectInState(*state, argvMO, false);

    for (int i=0; i<argc+1+envc+1+1; i++) {
      if (i==argc || i>=argc+1+envc) {
        // Write NULL pointer
        argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
      } else {
        char *s = i<argc ? argv[i] : envp[i-(argc+1)];
        int j, len = strlen(s);

        MemoryObject *arg =
            memory->allocate(len + 1, /*isLocal=*/false, /*isGlobal=*/true,
                             /*allocSite=*/state->pc->inst, /*alignment=*/8);
        if (!arg)
          klee_error("Could not allocate memory for function arguments");
        ObjectState *os = bindObjectInState(*state, arg, false);
        for (j=0; j<len+1; j++)
          os->write8(j, s[j]);

        // Write pointer to newly allocated and initialised argv/envp c-string
        argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
      }
    }
  }
  
  initializeGlobals(*state);

  processTree = new PTree(state);
  state->ptreeNode = processTree->root;
  run(*state);
  delete processTree;
  processTree = 0;

  // hack to clear memory objects
  delete memory;
  memory = new MemoryManager(NULL);

  globalObjects.clear();
  globalAddresses.clear();

  if (statsTracker)
    statsTracker->done();
}

unsigned Executor::getPathStreamID(const ExecutionState &state) {
  assert(pathWriter);
  return state.pathOS.getID();
}

unsigned Executor::getSymbolicPathStreamID(const ExecutionState &state) {
  assert(symPathWriter);
  return state.symPathOS.getID();
}

void Executor::getConstraintLog(const ExecutionState &state, std::string &res,
                                Interpreter::LogType logFormat) {

  switch (logFormat) {
  case STP: {
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    char *log = solver->getConstraintLog(query);
    res = std::string(log);
    free(log);
  } break;

  case KQUERY: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprPPrinter::printConstraints(info, state.constraints);
    res = info.str();
  } break;

  case SMTLIB2: {
    std::string Str;
    llvm::raw_string_ostream info(Str);
    ExprSMTLIBPrinter printer;
    printer.setOutput(info);
    Query query(state.constraints, ConstantExpr::alloc(0, Expr::Bool));
    printer.setQuery(query);
    printer.generateOutput();
    res = info.str();
  } break;

  default:
    klee_warning("Executor::getConstraintLog() : Log format not supported!");
  }
}

bool Executor::getSymbolicSolution(const ExecutionState &state,
                                   std::vector< 
                                   std::pair<std::string,
                                   std::vector<unsigned char> > >
                                   &res) {
  solver->setTimeout(coreSolverTimeout);

  ExecutionState tmp(state);

  // Go through each byte in every test case and attempt to restrict
  // it to the constraints contained in cexPreferences.  (Note:
  // usually this means trying to make it an ASCII character (0-127)
  // and therefore human readable. It is also possible to customize
  // the preferred constraints.  See test/Features/PreferCex.c for
  // an example) While this process can be very expensive, it can
  // also make understanding individual test cases much easier.
  for (unsigned i = 0; i != state.symbolics.size(); ++i) {
    const MemoryObject *mo = state.symbolics[i].first;
    std::vector< ref<Expr> >::const_iterator pi = 
      mo->cexPreferences.begin(), pie = mo->cexPreferences.end();
    for (; pi != pie; ++pi) {
      bool mustBeTrue;
      // Attempt to bound byte to constraints held in cexPreferences
      bool success = solver->mustBeTrue(tmp, Expr::createIsZero(*pi),

					mustBeTrue);
      // If it isn't possible to constrain this particular byte in the desired
      // way (normally this would mean that the byte can't be constrained to
      // be between 0 and 127 without making the entire constraint list UNSAT)
      // then just continue on to the next byte.
      if (!success) break;
      // If the particular constraint operated on in this iteration through
      // the loop isn't implied then add it to the list of constraints.
      if (!mustBeTrue) tmp.addConstraint(*pi);
    }
    if (pi!=pie) break;
  }

  std::vector< std::vector<unsigned char> > values;
  std::vector<const Array*> objects;
  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    objects.push_back(state.symbolics[i].second);
  bool success = solver->getInitialValues(tmp, objects, values);
  solver->setTimeout(0);
  if (!success) {
    klee_warning("unable to compute initial values (invalid constraints?)!");
    ExprPPrinter::printQuery(llvm::errs(), state.constraints,
                             ConstantExpr::alloc(0, Expr::Bool));
    return false;
  }
  
  for (unsigned i = 0; i != state.symbolics.size(); ++i)
    res.push_back(std::make_pair(state.symbolics[i].first->name, values[i]));
  return true;
}

void Executor::getCoveredLines(const ExecutionState &state,
                               std::map<const std::string*, std::set<unsigned> > &res) {
  res = state.coveredLines;
}

void Executor::doImpliedValueConcretization(ExecutionState &state,
                                            ref<Expr> e,
                                            ref<ConstantExpr> value) {
  abort(); // FIXME: Broken until we sort out how to do the write back.

  if (DebugCheckForImpliedValues)
    ImpliedValue::checkForImpliedValues(solver->solver, e, value);

  ImpliedValueList results;
  ImpliedValue::getImpliedValues(e, value, results);
  for (ImpliedValueList::iterator it = results.begin(), ie = results.end();
       it != ie; ++it) {
    ReadExpr *re = it->first.get();
    
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(re->index)) {
      // FIXME: This is the sole remaining usage of the Array object
      // variable. Kill me.
      const MemoryObject *mo = 0; //re->updates.root->object;
      const ObjectState *os = state.addressSpace.findObject(mo);

      if (!os) {
        // object has been free'd, no need to concretize (although as
        // in other cases we would like to concretize the outstanding
        // reads, but we have no facility for that yet)
      } else {
        assert(!os->readOnly && 
               "not possible? read only object with static read?");
        ObjectState *wos = state.addressSpace.getWriteable(mo, os);
        wos->write(CE, it->second);
      }
    }
  }
}

Expr::Width Executor::getWidthForLLVMType(llvm::Type *type) const {
  return kmodule->targetData->getTypeSizeInBits(type);
}

size_t Executor::getAllocationAlignment(const llvm::Value *allocSite) const {
  // FIXME: 8 was the previous default. We shouldn't hard code this
  // and should fetch the default from elsewhere.
  const size_t forcedAlignment = 8;
  size_t alignment = 0;
  llvm::Type *type = NULL;
  std::string allocationSiteName(allocSite->getName().str());
  if (const GlobalValue *GV = dyn_cast<GlobalValue>(allocSite)) {
    alignment = GV->getAlignment();
    if (const GlobalVariable *globalVar = dyn_cast<GlobalVariable>(GV)) {
      // All GlobalVariables's have pointer type
      llvm::PointerType *ptrType =
          dyn_cast<llvm::PointerType>(globalVar->getType());
      assert(ptrType && "globalVar's type is not a pointer");
      type = ptrType->getElementType();
    } else {
      type = GV->getType();
    }
  } else if (const AllocaInst *AI = dyn_cast<AllocaInst>(allocSite)) {
    alignment = AI->getAlignment();
    type = AI->getAllocatedType();
  } else if (isa<InvokeInst>(allocSite) || isa<CallInst>(allocSite)) {
    // FIXME: Model the semantics of the call to use the right alignment
    llvm::Value *allocSiteNonConst = const_cast<llvm::Value *>(allocSite);
    const CallSite cs = (isa<InvokeInst>(allocSiteNonConst)
                             ? CallSite(cast<InvokeInst>(allocSiteNonConst))
                             : CallSite(cast<CallInst>(allocSiteNonConst)));
    llvm::Function *fn =
        klee::getDirectCallTarget(cs, /*moduleIsFullyLinked=*/true);
    if (fn)
      allocationSiteName = fn->getName().str();

    klee_warning_once(fn != NULL ? fn : allocSite,
                      "Alignment of memory from call \"%s\" is not "
                      "modelled. Using alignment of %zu.",
                      allocationSiteName.c_str(), forcedAlignment);
    alignment = forcedAlignment;
  } else {
    llvm_unreachable("Unhandled allocation site");
  }

  if (alignment == 0) {
    assert(type != NULL);
    // No specified alignment. Get the alignment for the type.
    if (type->isSized()) {
      alignment = kmodule->targetData->getPrefTypeAlignment(type);
    } else {
      klee_warning_once(allocSite, "Cannot determine memory alignment for "
                                   "\"%s\". Using alignment of %zu.",
                        allocationSiteName.c_str(), forcedAlignment);
      alignment = forcedAlignment;
    }
  }

  // Currently we require alignment be a power of 2
  if (!bits64::isPowerOfTwo(alignment)) {
    klee_warning_once(allocSite, "Alignment of %zu requested for %s but this "
                                 "not supported. Using alignment of %zu",
                      alignment, allocSite->getName().str().c_str(),
                      forcedAlignment);
    alignment = forcedAlignment;
  }
  assert(bits64::isPowerOfTwo(alignment) &&
         "Returned alignment must be a power of two");
  return alignment;
}

void Executor::prepareForEarlyExit() {
  if (statsTracker) {
    // Make sure stats get flushed out
    statsTracker->done();
  }
}
///

Interpreter *Interpreter::create(LLVMContext &ctx, const InterpreterOptions &opts,
                                 InterpreterHandler *ih) {
  return new Executor(ctx, opts, ih);
}
