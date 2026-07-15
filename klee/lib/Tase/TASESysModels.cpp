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

using namespace llvm;
using namespace klee;

//AH: Our additions below. --------------------------------------
#include "tase_interp.h"
#include "API.h"

#include <iostream>
#include "klee/CVAssignment.h"
#include "klee/util/ExprUtil.h"
#include "klee/Constraints.h"
//#include "tase/TASEControl.h"
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/mman.h>
#include <errno.h>
#include <cxxabi.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <netdb.h>
#include <fcntl.h>
#include <fstream>
#include <byteswap.h>
#include <regex>
#include <sys/ioctl.h>
#include <vector>
#include <sys/sendfile.h>
#include <sys/stat.h>

//#include "../../../musl/arch/x86_64/pthread_arch.h"
//#include "../../../musl/src/internal/pthread_impl.h"
extern uint64_t scout_counter;
extern pid_t scout;

extern uint64_t instCtr;
extern uint64_t interpCtr;
extern uint64_t rodata_size;
extern uint16_t poison_val;
extern tase_greg_t * target_ctx_gregs;
extern klee::Interpreter * GlobalInterpreter;
extern MemoryObject * target_ctx_gregs_MO;
extern ObjectState * target_ctx_gregs_OS;
extern ExecutionState * GlobalExecutionStatePtr;
extern void * rodata_base_ptr;
extern std::stringstream worker_ID_stream;

uint64_t native_ret_off = 0;

//extern bool taseDebug;
//extern bool modelDebug;
extern bool bufferGuard;
extern bool skipFree;
extern bool taseManager;
//extern bool noLog;

extern bool gprsAreConcrete();
//extern void tase_exit(int);
extern void print_run_timers();
//extern void printCtx(tase_greg_t *);
inline bool tase_buf_has_taint(const void * addr, const int size);

bool tase_buf_has_taint (const void * ptr, const int size) {
  const uint16_t * checkBase = ((uint64_t) ptr) % 2 == 1 ? (uint16_t *) ((uint64_t) ptr - 1 ) : (uint16_t *) ptr;
  const int checkSize = ( ((uint8_t*) ptr + size + 1 ) - (uint8_t*) checkBase ) / 2;
  
  for ( int i = 0; i < checkSize; i++ ) {
    if ( *( checkBase + i ) == poison_val )
      return true;
  }
  return false;
}


bool roundUpHeapAllocations = true; //Round the size Arg of malloc, realloc, and calloc up to a multiple of 8
//This matters because it controls the size of the MemoryObjects allocated in klee.  Reads executed by
//some library functions (ex memcpy) may copy 4 or 8 byte-chunks of data at a time that cross over the edge
//of memory object buffers that aren't 4 or 8 byte aligned.

std::map<void *, void *> heap_guard_map; //


// For fopen/freopen/fclose etc
// need to intercept on fork/clone calls
// and reopen the files so we have unique file descriptions (as opposed to descriptors)
// so we have unique offsets into the file per-process
// OUR USAGE ASSUMES A FILE IS ALWAYS ACCESSED BY THE SAME PATHNAME IN A GIVEN PROGRAM
struct FileInfo {
  FILE* file;
  std::string original_name;
  std::string name;
  std::string mode;
  int offset;
};

std::vector<FileInfo> open_files;


void copy_file(std::string& src, std::string& dst) {
  int src_fd = open(src.c_str(), O_RDONLY, 0);
  int dst_fd = open(dst.c_str(), O_WRONLY | O_CREAT, 0644);

  struct stat stat_source;
  fstat(src_fd, &stat_source);
  
  sendfile(dst_fd, src_fd, 0, stat_source.st_size);
  close(src_fd);
  close(dst_fd);
}


extern "C" void renew_fds() {
  for( size_t i = 0; i < open_files.size(); i++ ) {
    open_files[i].offset = ftell(open_files[i].file);
    fflush(open_files[i].file);
    fclose(open_files[i].file);
    
    if( open_files[i].mode[0] != 'r' ) { // close + copy file, new name
      std::string oldname = open_files[i].name;
      open_files[i].name += "." + std::to_string(getpid());
      copy_file(oldname, open_files[i].name);
    }

    open_files[i].file = fopen(open_files[i].name.c_str(), open_files[i].mode.c_str());
    MOD_TASE("reopening file %s with handle 0x%lx at offset %d\n", open_files[i].name.c_str(), (uint64_t) open_files[i].file,  open_files[i].offset)
    fseek(open_files[i].file, open_files[i].offset, SEEK_SET);
  }
}



template<typename T, bool U>
struct as_helper;

template<typename T> T inline _as(tase_greg_t t);

template<typename T>
struct as_helper<T, true> {
  static T inline conv(tase_greg_t t){return (T) t.u64;}
};

template<typename T>
struct as_helper<T, false> {
  static T inline conv(tase_greg_t t){return _as<T>(t);}
};

template<typename T> T inline as(tase_greg_t t){return as_helper<T, std::is_pointer<T>::value>::conv(t);}

template<> uint64_t inline _as(tase_greg_t t){return t.u64;}
template<> int64_t inline _as(tase_greg_t t){return t.i64;}
template<> uint32_t inline _as(tase_greg_t t){return t.u32;}
template<> int32_t inline _as(tase_greg_t t){return t.i32;}
template<> int16_t inline _as(tase_greg_t t){return t.i16;}
template<> uint16_t inline _as(tase_greg_t t){return t.u16;}
template<> double inline _as(tase_greg_t t){return t.dbl;}
template<> char inline _as(tase_greg_t t){return (char) t.u8;}


#define _LOG DBG_TASE("Entering %s at interpCtr %ld\n", __func__, interpCtr)


void printBuf(FILE * f, void * buf, size_t count)
{
  fprintf(f,"Calling printBuf with count %ld\n", count);
  fflush(f);
  for (size_t i = 0; i < count; i++) {
    fprintf(f,"%02x", *((uint8_t *) buf + i));
    fflush(f);
  }
  fprintf(f,"\n\n");
  fflush(f);
}

//Used to restore concrete values for buffers that are
//entirely made up of constant expressions
void Executor::rewriteConstants(uint64_t base, size_t size) {
  MOD_TASE("Rewriting constant array\n")

  //Fast path -- if no taint in buffer, can't have exprs
  if (!tase_buf_has_taint((void *) base, size)) {
    return;
  }
  
  if (!(
	base > ((uint64_t) rodata_base_ptr)
	 &&
	base < (((uint64_t) rodata_base_ptr) + rodata_size)
	)
      ) {
    MOD_TASE("Base does not appear to be in rodata\n")
  } else {
    MOD_TASE("Found base in rodata.  Returning from rewriteConstants without doing anything\n")
    return;
  }
  
  for (size_t i = 0; i < size; i++) {

    //We're assuming
    //1. Every byte's 2-byte aligned buffer containing it has been mapped with a MO/OS at some point.
    //2. It's OK to duplicate some of these read/write ops
    uint64_t writeAddr;
    if( (base + i) %2 != 0)
      writeAddr = base + i -1;
    else
      writeAddr = base + i;
    
    ref<Expr> val = tase_helper_read(writeAddr, 2);
    tase_helper_write(writeAddr, val);

  }
  if ( taseDebug > 0 ) {
    LOG_TASE("End result:\n")
    printBuf(stdout, (void *) base, size);
  }
}

/*
// void __assert_fail(const char * assertion, const char * file, unsigned int line, const char * function)
void Executor::model_assert_fail(){
  if( !noLog ) {
    _LOG
  }

  int count = 0;
  uint64_t *s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  char *assertion;
  char *file;
  unsigned int line;
  char *function;
  get_vals(count, s_offset, __func__, assertion, file, line, function);
  __assert_fail(assertion, file, line, function);
  do_ret();
}
*/

void Executor::model_tase_make_symbolic() {
  if( !isBufferEntirelyConcrete((uint64_t) &target_ctx_gregs[GREG_RDX], 3*8) )  { // RDX/RSI/RDI are contiguous in ctx
    ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
    ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
    ref<Expr> arg3Expr = target_ctx_gregs_OS->read(GREG_RDX * 8, Expr::Int64);

    if  ( !isa<ConstantExpr>(arg1Expr) || !isa<ConstantExpr>(arg2Expr) || !isa<ConstantExpr>(arg3Expr) ){
      LOG_TASE("ERROR in model_tase_make_symbolic -- args must all be concrete. \n");
      std::exit(EXIT_FAILURE);
    }
  }
  
  uint64_t addr = target_ctx_gregs[GREG_RDI].u64;
  uint64_t size = target_ctx_gregs[GREG_RSI].u64; //Todo -- impose a reasonable upper limit on size.
  char * name = (char *) target_ctx_gregs[GREG_RDX].u64;
  

  if (clientName == "TETRINET") {
    tetrinet_make_symbolic(addr, size, name);  
  } else {
    tase_make_symbolic_internal(addr, size, name);
  }
  calleeKillDeadRegs();
  do_ret();
}


extern bool success;

void Executor::model_exit_tase() {
  _LOG
  
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;
  
  int status;
  get_val(count, s_offset, __func__, status);

  LOG_TASE("Exit called with status: %d\n", status);
  success = status == EXIT_SUCCESS;
  
  if( success ) {
    print_run_timers();
    LOG_TASE("Successfully exited from target.  Shutting down with %ld x86 blocks interpreted \n%ld total LLVM IR instructions interpreted\n", interpCtr, instCtr);

    if( !(klee::verTestType == VerTestType::SINGLEMSGVER || klee::verTestType == VerTestType::VERIFY || klee::verTestType == VerTestType::TRAIN) ) {  // default is REPLAY
      worker_success(Stopped, Running); //We don't need to send success for verification tests when the client exits.
    }
  }
  
  LOG_TASE("Exiting from program \n");LOG_FLUSH();
  exit(status);
}

void Executor::model_exit_tase_success() {
  _LOG
  
  print_run_timers();
  LOG_TASE("Successfully exited from target.  Shutting down with %ld x86 blocks interpreted \n%ld total LLVM IR instructions interpreted\n", interpCtr, instCtr)
  worker_success(Stopped, Running);
  success = true;
  exit(EXIT_SUCCESS);
}



void Executor::model_usleep(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                 
  ++s_offset;

  //  useconds_t usec;
  unsigned int usec;
  get_val(count, s_offset, __func__, usec);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) usleep(usec), Expr::Int64);
  tase_helper_write((uint64_t)&target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}




void Executor::model_putchar(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  char c;
  get_val(count, s_offset, __func__, c);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) putchar(c), Expr::Int64);
  tase_helper_write((uint64_t)&target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

//Todo -- figure out the endianness issue with
//copying 2 bytes at a time in the slow unaligned path
void Executor::model_memcpy_tase() {
  _LOG

  double T0 = util::getWallTime();

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;
  void* dst;
  void* src;
  //PICK UP HERE
  size_t s;
  //This crazy-looking fix is for a case that comes up verifying mavlink on O2.  For some reason,
  //we enter memcpy with the size argument a symbolic expression, which actually happens to
  //only have 1 concrete value when we consult the solver and global constraints.
  ref<Expr> sizeArg = tase_helper_read((uint64_t) &target_ctx_gregs[GREG_RDX].u64, 8);
  if ((isa<ConstantExpr>(sizeArg))) {
    LOG_TASE("sizeArg is a constant expr \n");
  } else {
    LOG_TASE("sizeArg isn't constant expr \n");
    ExecutionState dummy = ExecutionState(getDepCons(sizeArg,false));
    std::vector<ref<Expr>> vals = getNPossibleValues(dummy, sizeArg, 100);
    LOG_TASE("%ld possible values \n", vals.size());
    
    if (vals.size() == 1) {
      MOD_TASE("Only one value -- concretizing size arg \n");
      tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RDX], vals[0]);
      MOD_TASE("RDX is now 0x%lx \n", target_ctx_gregs[GREG_RDX].u64);
    }
  }
  
  get_vals(count, s_offset, __func__, dst, src, s);

  //void * dst = (void *) target_ctx_gregs[GREG_RDI].u64;
  //void * src = (void *) target_ctx_gregs[GREG_RSI].u64;

  LOG_TASE("model_memcpy from 0x%lx to 0x%lx \n", (uint64_t) src, (uint64_t) dst);LOG_FLUSH();
  int size = (int) target_ctx_gregs[GREG_RDX].u64;

  /*
  LOG_TASE("Printing source: \n");LOG_FLUSH();
  for (int i = 0; i < size; i++) {
    ref<Expr> val = tase_helper_read((uint64_t) (( (uint8_t *) src ) +i), 1);
    LOG_TASE("Byte %d: %s \n",i, val->dumpToStr().c_str());  LOG_FLUSH();
  }

  LOG_TASE("Printing dest: \n");LOG_FLUSH();
  for (int i = 0; i < size; i++) {
    ref<Expr> val = tase_helper_read((uint64_t) (( (uint8_t *) dst ) +i), 1);
    LOG_TASE("Byte %d: %s \n",i, val->dumpToStr().c_str());  LOG_FLUSH();
  }
  
  */
  int zero = 0; //Force kill rcx -- Should be fine because it's caller-saved.
  ref<ConstantExpr> zeroExpr = ConstantExpr::create((uint64_t) zero, Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RCX], zeroExpr);
  
  if (isBufferEntirelyConcrete((uint64_t) dst, s) && isBufferEntirelyConcrete((uint64_t) src, s)) {
    LOG_TASE("Memcpy fast path  \n");LOG_FLUSH();
    rewriteConstants((uint64_t) dst, s);
    rewriteConstants((uint64_t) src, s);
    memcpy(dst, src, s);
  } else {
    LOG_TASE("Memcpy slow path \n");LOG_FLUSH();
    //Fast path aligned case
    if ((((uint64_t) dst) %2 == 0) && (((uint64_t) src) % 2 == 0) && (((uint64_t) s) %2 == 0)) {
      for (uint i = 0; i < s; i++) {
	  
        if (i%2 == 0
            && *((uint16_t *) ((uint64_t) src + i) ) != poison_val
            && *((uint16_t *) ((uint64_t) dst + i) ) != poison_val
	      )
        {
          *((uint16_t *) ((uint64_t) dst + i) )  = *((uint16_t *) ((uint64_t) src + i) );
          i++;
        } else {

          ref <Expr> b = tase_helper_read((uint64_t) src + i, 1);
          tase_helper_write((uint64_t) dst+i, b);
	    
        }
      }

    } else {
      for (uint i = 0; i < s; i++) {
        ref <Expr> b = tase_helper_read((uint64_t) src + i, 1);
        tase_helper_write((uint64_t) dst+i, b);
      }
    }
  }
    
  double T1 = util::getWallTime();
  
  LOG_TASE("memcpy took %f seconds\n", T1-T0)
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) dst, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}


//Todo -- Just rip it out?
//Eliminate dead and reserved registers in case they contain
//symbolic taint.  Used to help avoid interpreting through
//prohibitive functions.
void Executor::killDeadRegsPreCall() {
  ref<ConstantExpr> zeroExpr = ConstantExpr::create((uint64_t) 0, Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_R14].u64, zeroExpr);
}


//Utility function to fake x86_64 retq instruction
//at end of model.
void Executor::do_ret() {
  target_ctx_gregs[GREG_RIP].u64 = *((uint64_t*) target_ctx_gregs[GREG_RSP].u64);
  target_ctx_gregs[GREG_RSP].u64 += 8;
}



template<typename T>
void inline Executor::get_val(int& count, uint64_t* &s_offset, const std::string& reason, T& t){
  const auto rr = reason + "\n";

  if( count < 6 ) {
    int idx = count < 4 ? (5-count) : (4+count);

    if( !isBufferEntirelyConcrete((uint64_t) &target_ctx_gregs[idx], 8) ) {
      ref<Expr> aref = target_ctx_gregs_OS->read(idx*8, Expr::Int64);

      if( !isa<ConstantExpr>(aref) ) {
	ref<Expr> aref2 = toConstant(*GlobalExecutionStatePtr, aref, rr.c_str());
	tase_helper_write((uint64_t) &target_ctx_gregs[idx], aref2);
      }
    }
    
    t = as<T>(target_ctx_gregs[idx]);
    ++count;
    
  } else {
    if( !isBufferEntirelyConcrete((uint64_t) s_offset, 8) ) {
      ref<Expr> aref = tase_helper_read((uint64_t) s_offset, 8);

      if( !isa<ConstantExpr>(aref) ) {
	ref<Expr> aref2 = toConstant(*GlobalExecutionStatePtr, aref, rr.c_str());
	tase_helper_write((uint64_t) s_offset, aref2);
      }
    }

    t = *((T*) s_offset);
    ++s_offset;
  }
}


// template<typename T>
// void Executor::get_val_va(uint64_t* &s_offset, const std::string& reason, T& t){
//   auto rr = reason + "\n";
//   ref<Expr> aref = tase_helper_read((uint64_t) s_offset, 8);
//   if(isa<ConstantExpr>(aref)){
//     t = *((T*)s_offset);
//   } else {
//     ref<ConstantExpr> aref2 = toConstant(*GlobalExecutionStatePtr, aref, rr.c_str());
//     tase_helper_write((uint64_t) s_offset, aref2);
//   }
//   ++s_offset;
// }


template<typename U, typename... T>
void inline Executor::get_vals(int& count, uint64_t* &s_offset, const std::string& reason, U& u, T&... ts){
  get_val(count, s_offset, reason, u);
  get_vals(count, s_offset, reason, ts...);
}

template<typename... T>
void inline Executor::get_vals(int& count, uint64_t* &s_offset, const std::string& reason){
  return;
}

/*
uint64_t * get_val(int fpcount, uint64_t *s_offset, double& t, const char* reason){
  if(fpcount < 16){
    int idx = fpcount / 2;
    bool even = fpcount % 2 == 0
    auto ref = target_ctx_xmms_OS->read(idx*XMMREG_SIZE + (even ? 0 : 1), Expr::Int64); // Width given here, not a type
    if(isa<ConstantExpr>(ref)){
      t = target_ctx_xmms[idx][(even ? 0 : 1)];
    }
  } else {
    auto ref = tase_helper_read(s_offset);
    if(isa<ConstantExpr>(ref)){
      t = *s_offset;
    } else {
      auto ref2 = toConstant(*GlobalExecutionStatePtr, ref, reason);
      tase_helper_write((uint64_t) s_offset, ref2);
    }
    return s_offset + 8;
  }
  return s_offset;
}
*/


template<typename... Ts>
std::string Executor::model_printf_base_helper(int& count, uint64_t* &s_offset, const std::string& reason, char type, const std::string& ff, const std::string& out, Ts... ts){
  char outstr[255];

  switch(type){
    case 'd': //signed int
    case 'i':
    {
      // printf will down-convert (u)int64_t to whatever was specified in fmt string
      int64_t arg;
      get_val(count, s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;
    case 'u': //unsigned int
    case 'o':
    case 'x':
    case 'X':
      // same as above but unsigned
    {
      uint64_t arg;
      get_val(count, s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;
    case 'f': // fp - the difference in size matters here. Check if x[3] is L or not? for now just ignore - no long doubles allowed!
    case 'F':
    case 'e':
    case 'E':
    case 'g':
    case 'G':
    case 'a':
    case 'A':
    {
      double arg;
      get_val(count, s_offset, reason, arg);
      sprintf_helper( &outstr[0], ff, ts..., arg);
      //fpcount++;
    }
    break;

    case 'c': // char
    {
      char arg;
      get_val(count, s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;
    case 's': // char*
    {
      char* arg;
      //      std::cout << "printf get_val<char*>: \"" << arg << "\"" << std::endl;
      get_val(count, s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;

    case 'n': // ptr to int, stores the # chars printed so far and elides the %n
      // save out.length() to the pointer
    {
      int* arg;
      get_val(count, s_offset, reason, arg);
      *arg = out.length();
    }
    break;
  }

  return type == 'n' ? "" : std::string(outstr);
}


template<typename T>
void Executor::sanitize_va_arg(T& t){
  ref<Expr> aref = tase_helper_read((uint64_t) &t, sizeof(T));
  if(isa<ConstantExpr>(aref)){
    return;
  } else {
    ref<ConstantExpr> aref2 = toConstant(*GlobalExecutionStatePtr, aref, "sanitize_va_arg\n");
    tase_helper_write((uint64_t) &t, aref2);
  }
}


template<typename... Ts>
std::string Executor::model_printf_base_helper_va(uint64_t* &s_offset, const std::string& reason, char type, const std::string& ff, const std::string& out, va_list lst, Ts... ts){
  char outstr[255];

  switch(type){
    case 'd': //signed int
    case 'i':
    {
      // printf will down-convert (u)int64_t to whatever was specified in fmt string
      int64_t arg = va_arg(lst, int64_t);
 //     sanitize_va_arg(arg);
      //get_val_va(s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;
    case 'u': //unsigned int
    case 'o':
    case 'x':
    case 'X':
      // same as above but unsigned
    {
      uint64_t arg = va_arg(lst, uint64_t);
 //     sanitize_va_arg(arg);
      //get_val_va(s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;
    case 'f': // fp - the difference in size matters here. Check if x[3] is L or not? for now just ignore - no long doubles allowed!
    case 'F':
    case 'e':
    case 'E':
    case 'g':
    case 'G':
    case 'a':
    case 'A':
    {
      double arg = va_arg(lst, double);
//      sanitize_va_arg(arg);
      //get_val_va(s_offset, reason, arg);
      sprintf_helper( &outstr[0], ff, ts..., arg);
      //fpcount++;
    }
    break;

    case 'c': // char
    {
      char arg = va_arg(lst, char);
 //     sanitize_va_arg(arg);
      //get_val_va(s_offset, reason, arg);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;
    case 's': // char*
    {
      char* arg = va_arg(lst, char*);
 //     sanitize_va_arg(arg);
      //get_val_va(s_offset, reason, arg);
      //      printf("printf get_val<char*>: %d, \"%s\"\n", ts..., arg);
      //      fflush(stdout);
      sprintf_helper(&outstr[0], ff, ts..., arg);
    }
    break;

    case 'n': // ptr to int, stores the # chars printed so far and elides the %n
      // save out.length() to the pointer
    {
      int* arg = va_arg(lst, int*);
//      sanitize_va_arg(arg);
      //get_val_va(s_offset, reason, arg);
      *arg = out.length();
    }
    break;
  }

  return type == 'n' ? "" : std::string(outstr);
}


void Executor::sprintf_helper(char* outstr, const std::string& ff, ...){
  va_list args;
  va_start(args, ff);
  vsprintf(outstr, ff.c_str(), args);
  va_end(args);
}



std::string Executor::model_printf_base(int& count, uint64_t* &s_offset, const std::string& reason){
  char * fmtc;
  get_val(count, s_offset, reason, fmtc);

  std::string fmt = std::string(fmtc);
  //  if( modelDebug ){
  //    std::cout << reason << " with fmt string: \"" << fmt << "\"" << std::endl;
  //  }
  MOD_TASE("%s with fmt string: \"%s\"\n", reason.c_str(), fmt.c_str())

  // possibly useful alternative for doubles:
  // check al
  // if al is zero, no fp args
  // else dump xmm 0-7 to array

  std::regex specifier("%([-+#0 ])?([0-9*])?(.[0-9]+|.[*])?(hh|h|l|ll|j|z|t|L)?([diouxXfFeEgGaAcspn])", std::regex::egrep);
  auto match_begin = std::sregex_iterator(fmt.begin(), fmt.end(), specifier);
  auto out = std::string();
  auto last = fmt.cbegin();
  for(auto it = match_begin; it != std::sregex_iterator(); ++it){
    auto x = *it;
    out += fmt.substr(last - fmt.begin(), x[0].first - last); // non-format characters up to current match
    last = x[5].second;

    char type = x[5].str()[0];
    std::string ff = x.str(0);

    int width;
    int precision;

    bool gw = x[2].str().find('*') != std::string::npos;
    bool gp = x[3].str().find('*') != std::string::npos;

    if(gw){
      get_val(count, s_offset, reason, width);
      //      std::cout << ff << " width: " << width << std::endl;
    }

    if(gp){
      get_val(count, s_offset, reason, precision);
      //      std::cout << ff << " precision: " << precision << std::endl;
    }

    out += gw ? (gp ? model_printf_base_helper(count, s_offset, reason, type, ff, out, width, precision)  :
                      model_printf_base_helper(count, s_offset, reason, type, ff, out, width)  ) :
                (gp ? model_printf_base_helper(count, s_offset, reason, type, ff, out, precision)  :
                      model_printf_base_helper(count, s_offset, reason, type, ff, out)  );
  }
  out += fmt.substr(last - fmt.begin(), fmt.end() - last);
  return out;
}




template<typename T>
struct arr_type;

template<typename T>
struct arr_type<T[1]> {typedef T type;};

typedef arr_type<va_list>::type va_val;

std::string Executor::model_printf_base_va(int& count, uint64_t* &s_offset, const std::string& reason){
  char * fmtc;
  va_list lst;
  va_val* x;
  get_vals(count, s_offset, reason, fmtc, x);
  lst[0] = *x;
  struct {
    int32_t a;
    int32_t b;
    uint64_t c;
    uint64_t d;} t;
  std::memcpy((void*) &t, (void*) x, sizeof(x));
  //  std::cout << "va_list: " << t.a << ", " << t.b << ", " << std::hex << t.c << ", " << t.d << std::dec << std::endl;

  std::string fmt = std::string(fmtc);
  //  if(modelDebug){
  //    std::cout << reason << " with fmt string: \"" << fmt << "\"" << std::endl;
  //  }

  // possibly useful alternative for doubles:
  // check al
  // if al is zero, no fp args
  // else dump xmm 0-7 to array

  std::regex specifier("%([-+#0 ])?([0-9*])?(.[0-9]+|.[*])?(hh|h|l|ll|j|z|t|L)?([diouxXfFeEgGaAcspn])", std::regex::egrep);
  auto match_begin = std::sregex_iterator(fmt.begin(), fmt.end(), specifier);
  auto out = std::string();
  auto last = fmt.cbegin();
  for(auto it = match_begin; it != std::sregex_iterator(); ++it){
    auto x = *it;
    out += fmt.substr(last - fmt.begin(), x[0].first - last); // non-format characters up to current match
    last = x[5].second;

    char type = x[5].str()[0];
    std::string ff = x.str(0);

    int width;
    int precision;

    bool gw = x[2].str().find('*') != std::string::npos;
    bool gp = x[3].str().find('*') != std::string::npos;

    if(gw){
      get_val(count, s_offset, reason, width);
      //      std::cout << ff << " width: " << width << std::endl;
    }

    if(gp){
      get_val(count, s_offset, reason, precision);
      //      std::cout << ff << " precision: " << precision << std::endl;
    }

    out += gw ? (gp ? model_printf_base_helper_va(s_offset, reason, type, ff, out, lst, width, precision)  :
                      model_printf_base_helper_va(s_offset, reason, type, ff, out, lst, width)  ) :
                (gp ? model_printf_base_helper_va(s_offset, reason, type, ff, out, lst, precision)  :
                      model_printf_base_helper_va(s_offset, reason, type, ff, out, lst)  );
  }
  out += fmt.substr(last - fmt.begin(), fmt.end() - last);
  va_end(lst);
  return out;
}

// specifiers:
// %([-+#0 ])?([0-9*])?(.[0-9]+|.*)?(length)?(type)
// type/length table: see here https://cplusplus.com/reference/cstdio/printf/
// *-items -> extra arg given to fill in, precedes the value to be interpolated
// abi reference: https://www.intel.com/content/dam/develop/external/us/en/documents/mpx-linux64-abi.pdf
// printf(const char * fmt, ...)
void Executor::model_printf(){
  _LOG
    
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  std::string out = model_printf_base(count, s_offset, __func__);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) printf("%s", out.c_str()), Expr::Int64);
  tase_helper_write((uint64_t)&target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


void Executor::model_sprintf(){
  _LOG
      
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  char* argout;
  get_val(count, s_offset, __func__, argout);

  std::string out = model_printf_base(count, s_offset, __func__);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) sprintf(argout, "%s", out.c_str()), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


void Executor::model_fprintf(){
  _LOG
    
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  FILE* argout;
  get_val(count, s_offset, __func__, argout);

  std::string out = model_printf_base(count, s_offset, __func__);
  LOG_TASE("fprintf string: %s", out.c_str())
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) fprintf(argout, "%s", out.c_str()), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

void Executor::model_vsnprintf(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  char * argout;
  size_t size;
  get_vals(count, s_offset, __func__, argout, size);

  std::string out = model_printf_base_va(count, s_offset, __func__);
  sprintf(argout, "%s", out.substr(0, size-1 <= out.size() ? size-1 : out.size()).c_str());
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) out.size(), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


// sprintf but allocate a c str large enough, pass to char**. va_list
void Executor::model_vasprintf(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  char ** argout;
  get_val(count, s_offset, __func__, argout);

  std::string out = model_printf_base_va(count, s_offset, __func__);

  char * outstr = (char*) calloc(1, (out.size()+1)*sizeof(char));
  tase_map_buf((uint64_t) outstr, (out.size()+1)*sizeof(char), "vasprintf outstr");
  argout = &outstr;
  strcpy(outstr, out.c_str());
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) out.size(), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


void Executor::model_sigemptyset(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  sigset_t * set;
  get_val(count, s_offset, __func__, set);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) sigemptyset(set), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

void Executor::model_sigfillset(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  sigset_t * set;
  get_val(count, s_offset, __func__, set);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) sigfillset(set), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

void Executor::model_sigaddset(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  sigset_t * set;
  int signum;
  get_vals(count, s_offset, __func__, set, signum);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) sigaddset(set, signum), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

void Executor::model_sigaction(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int signum;
  struct sigaction * set;
  struct sigaction * oldset;
  get_vals(count, s_offset, __func__, signum, set, oldset);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) sigaction(signum, set, oldset), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


//int sigprocmask(int how, const sigset_t *restrict set,
//                       sigset_t *restrict oldset);
void Executor::model_sigprocmask(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int how;
  sigset_t * set;
  sigset_t * oldset;
  get_vals(count, s_offset, __func__, how, set, oldset);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) sigprocmask(how, set, oldset), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


void Executor::model_gethostname(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  char* name;
  size_t len;
  get_vals(count, s_offset, __func__, name, len);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) gethostname(name, len), Expr::Int64);
  tase_helper_write((int64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

// for samba, which calls once with a single int* param in varargs
void Executor::model_ioctl(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int fd;
  int request;
  int *value;
  get_vals(count, s_offset, __func__, fd, request, value);
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) ioctl(fd, request, value), Expr::Int64);
  tase_helper_write((int64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}



extern int * __errno_location();

void Executor::model___errno_location() {
  _LOG

  //Perform the call
  int * res = __errno_location();
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  //If it doesn't exit, back errno with a memory object.
  ObjectPair OP;
  ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP)) {
    MOD_TASE("errno var appears to have MO already backing it \n")
  } else {
    MOD_TASE("Creating MO to back errno at 0x%lx with size 0x%lx \n", (uint64_t) res, sizeof(int))
    MemoryObject * newMO = addExternalObject(*GlobalExecutionStatePtr, (void *) res, sizeof(int), false, "Errno struct");
    const ObjectState * newOSConst = GlobalExecutionStatePtr->addressSpace.findObject(newMO);
    ObjectState *newOS = GlobalExecutionStatePtr->addressSpace.getWriteable(newMO,newOSConst);
    newOS->concreteStore = (uint8_t *) res;
  }
  
  do_ret();//fake a ret
}



void Executor::model_exit() {

  LOG_TASE("Found call to exit.  TASE should shutdown.\n")
  
  //Todo: Make a flag to only print round/pass for multipass
  //printf("IMPORTANT: Worker exiting from terminal path in round %d pass %d from model_exit \n", round_count, pass_count);
  //  worker_exit();
  exit(1);
}

//http://man7.org/linux/man-pages/man2/write.2.html
//ssize_t write(int fd, const void *buf, size_t count);
//This is NOT the model used for
//verification socket writes: see model_writesocket
void Executor::model_write() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;
  
  int fd;
  void *buf; 
  size_t wcount;

  get_vals(count, s_offset, __func__, fd, buf, wcount);
  
  char * theBuf = (char *) buf;

  if ( taseDebug > 0 ) {
    char printMe [wcount];
    strncpy (printMe, theBuf, wcount);
    if( printMe[wcount-1] == '\n' )
      printMe[wcount-1] = '\0';
    
    LOG_TASE("Found call to write.  Buf appears to be: \n\"%s\"\n", printMe)
  }

  uint64_t res = write(fd, buf, wcount);
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX].u64, resExpr);
  
  do_ret();//fake a ret

}

void Executor::model___printf_chk() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int flag;
  char* fmt;
  get_vals(count, s_offset, __func__, flag, fmt);
    //Ignore varargs for now and just print the second arg
  //  std::cout << "Second arg to __printf_chk is " <<  fmt << std::endl;
  LOG_TASE("Second arg to __printf_chk is %s\n", fmt)
  ref<ConstantExpr> zeroResultExpr = ConstantExpr::create(0, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, zeroResultExpr);
    
  do_ret();
}

//https://man7.org/linux/man-pages/man3/isatty.3.html
//int isatty(int fd);

void Executor::model_isatty() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int fd;
  get_val(count, s_offset, __func__, fd);

  int res = isatty(fd);
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}



//https://linux.die.net/man/3/fileno
//int fileno(FILE *stream); 
void Executor::model_fileno() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;
  
  FILE* file;
  get_val(count, s_offset, __func__, file);

  // if( taseDebug ) {
  //   std::cout << "fileno call on handle 0x" << std::hex << reinterpret_cast<uint64_t>(file) << std::dec << std::endl;
  // }
  DBG_TASE("fileno call on handle 0x%lx\n", reinterpret_cast<uint64_t>(file))
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) fileno(file), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}

//http://man7.org/linux/man-pages/man2/fcntl.2.html
//int fcntl(int fd, int cmd, ... /* arg */ );
void Executor::model_fcntl() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int fd;
  int cmd;
  int flag;
  get_vals(count, s_offset, __func__, fd, cmd, flag);

  if ( cmd == F_SETFL && flag == O_NONBLOCK) {
    //    std::cout << "fcntl call to set fd as nonblocking" << std::endl;
    LOG_TASE("fcntl call to set fd as nonblocking\n")
  } else {
    //    std::cout << "fcntl called with unmodeled args" << std::endl;
    LOG_TASE("fcntl called with unmodeled args\n")
  }

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) 0, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}


//http://man7.org/linux/man-pages/man2/stat.2.html
//int stat(const char *pathname, struct stat *statbuf);
//Todo: Make option to return symbolic result, and proprerly inspect input
void Executor::model_stat() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  char* pathname;
  struct stat* statbuf;
  get_vals(count, s_offset, __func__, pathname, statbuf);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) stat(pathname, statbuf), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}


//Just returns the current process's pid.  We can make this symbolic if we want later, or force a val
//that returns the same number regardless of worker forking.
void Executor::model_getpid() {
  _LOG
  int pid = getpid();
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) pid, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();

}

//uid_t getuid(void)
//http://man7.org/linux/man-pages/man2/getuid.2.html
//Todo -- determine if we should fix result, see if uid_t is ever > 64 bits
void Executor::model_getuid() {
  _LOG
  uid_t uidResult = getuid();
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) uidResult, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//Fake a ret
  
}

//uid_t geteuid(void)
//http://man7.org/linux/man-pages/man2/geteuid.2.html
//Todo -- determine if we should fix result prior to forking, see if uid_t is ever > 64 bits
void Executor::model_geteuid() {
  _LOG
  uid_t euidResult = geteuid();
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) euidResult, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//Fake a ret

}

//gid_t getgid(void)
//http://man7.org/linux/man-pages/man2/getgid.2.html
//Todo -- determine if we should fix result, see if gid_t is ever > 64 bits
void Executor::model_getgid() {
  _LOG
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) getgid(), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//Fake a ret

}

//gid_t getegid(void)
//http://man7.org/linux/man-pages/man2/getegid.2.html
//Todo -- determine if we should fix result, see if gid_t is ever > 64 bits
void Executor::model_getegid() {
  _LOG

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) getegid(), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();//Fake a ret
}

//char * getenv(const char * name)
//http://man7.org/linux/man-pages/man3/getenv.3.html
//Todo: This should be generalized, and also technically should inspect the input string's bytes
void Executor::model_getenv() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  char* name;
  get_val(count, s_offset, __func__, name);
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) getenv(name), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//Fake a ret
}





//time_t time(time_t *tloc);
// http://man7.org/linux/man-pages/man2/time.2.html
void Executor::model_time() {
  _LOG
  //ABH: I made the time call deterministic so it was easier to compare different
  //executions of one of our verified clients (I believe it was samba?) which
  //uses time values for some of the logic.
  LOG_TASE("Making time call deterministic \n");
  
  time_t res = 123456;
  
  time_t * inTime = (time_t *) target_ctx_gregs[GREG_RDI].u64;
  if (inTime != NULL) {
    *inTime = res;
  }
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//fake a ret
  LOG_TASE("Leaving model_time \n");

  /*
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  time_t* tloc;
  get_val(count, s_offset, __func__, tloc);
  time_t res = time(tloc);

  LOG_TASE("timeString is %s\nSize of timeVal is %lu\n", ctime(tloc), sizeof(time_t))
    
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
  */
}



//struct tm *gmtime(const time_t *timep);
//https://linux.die.net/man/3/gmtime
void Executor::model_gmtime() {
  _LOG
    
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  
  if  (
       (isa<ConstantExpr>(arg1Expr)) ) {
    //Do call
    struct tm * res = gmtime( (time_t *) target_ctx_gregs[GREG_RDI].u64);
    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    char timeBuf[30];
    strftime(timeBuf, 30, "%Y-%m-%d %H:%M:%S", res);

    LOG_TASE("gmtime result is %s \n", timeBuf)
    
    //If it doesn't exit, back returned struct with a memory object.
    ObjectPair OP;
    ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP)) {
      LOG_TASE("model_gmtime result appears to have MO already backing it \n")
    } else {
      LOG_TASE("Creating MO to back tm at 0x%lx with size 0x%lx \n", (uint64_t) res, sizeof(struct tm))

      MemoryObject * newMO = addExternalObject(*GlobalExecutionStatePtr, (void *) res, sizeof(struct tm), false, "gmtime struct");
      const ObjectState * newOSConst = GlobalExecutionStatePtr->addressSpace.findObject(newMO);
      ObjectState *newOS = GlobalExecutionStatePtr->addressSpace.getWriteable(newMO,newOSConst);
      newOS->concreteStore = (uint8_t *) res;
    }
    
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    do_ret();//fake a ret
    
  } else {
    concretizeGPRArgs(1, "model_gmtime");
    model_gmtime();
  }

}

//int gettimeofday(struct timeval *tv, struct timezone *tz);
//http://man7.org/linux/man-pages/man2/gettimeofday.2.html
//Todo -- properly check contents of args for symbolic content, allow for symbolic returns
void Executor::model_gettimeofday() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  struct timeval *tv;
  struct timezone *tz;
  
  get_vals(count, s_offset, __func__, tv, tz);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) gettimeofday(tv, tz), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//fake a ret
}


size_t roundUp(size_t input, size_t multiple) {  
  if (input % multiple == 0)
    return input;
  else {
    size_t divRes = input/multiple;
    return (divRes +1)* multiple;
  }
}

//void *calloc(size_t nmemb, size_t size);
//https://linux.die.net/man/3/calloc

void Executor::model_calloc() {
  _LOG
    
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  
  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) ) {

    size_t nmemb = target_ctx_gregs[GREG_RDI].u64;
    size_t size  = target_ctx_gregs[GREG_RSI].u64;

    size_t initNmemb;
    if (bufferGuard) {
      initNmemb = nmemb;
      //Need a better way to adjust up for the extra bufferguard bytes for size > 1.  Maybe just
      //re-route call through malloc?
      
      nmemb += 4 + 16; // 4 bytes for  the psn, plus two 8-byte buffers between psn and the
      //allocated space.  Our poison checking in the compiler sometimes conservatively promotes
      //read/write checks (e.g., an 8 byte write to a 16 byte check) when it can't determine
      //alignment information, so the extra 8-byte buffers should help with that.
      LOG_TASE("Requesting calloc of size %lu for bufferGuard on heap \n", initNmemb * size)
    }


    
    
    void * res = calloc(nmemb, size);

    
    
    size_t numBytes = size*nmemb;

    //Todo -- refactor and roundup work properly with and without bufferguard.
    //if (roundUpHeapAllocations)
    // numBytes = roundUp(numBytes,8);

    void * returnedBuf;
    if (bufferGuard) {
      returnedBuf = (void *) ((uint64_t) res + 2 + 8);
      //Need to be able to line up returned ptr vs actual buf later when free is called.
      DBG_TASE("bufferGuard obtained mapping on heap at 0x%lx \nbufferGuard returning ptr at 0x%lx \n", (uint64_t) res, (uint64_t) returnedBuf)
      heap_guard_map.insert(std::pair<void *, void *>(returnedBuf, res));

    } else {
      returnedBuf = res;
    }

    if (bufferGuard) {
      tase_map_buf((uint64_t) returnedBuf, initNmemb * size + 6, "calloc return buffer");
      //Poison edges around buffer
      * ((uint16_t *) (res)) = poison_val;
      void * endAddr =(void *)( (uint64_t) res + 2 + 8 + (initNmemb * size)  + 8);
      *((uint16_t *) (endAddr)) = poison_val;
    } else {
      tase_map_buf((uint64_t) returnedBuf, numBytes, "calloc return buffer");
    }

    LOG_TASE("calloc at 0x%lx for 0x%lx bytes \n", (uint64_t) res, numBytes)

    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) returnedBuf, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

    do_ret();//fake a ret
    
  } else {
    concretizeGPRArgs(2, "model_calloc");
    model_calloc();
  }    
}



//void *realloc(void *ptr, size_t size);
//https://linux.die.net/man/3/realloc
//Todo: Set up additional memory objects if realloc adds extra space
void Executor::model_realloc() {
  _LOG
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  ref<Expr> arg2Expr = target_ctx_gregs_OS->read(GREG_RSI * 8, Expr::Int64);
  if  (
       (isa<ConstantExpr>(arg1Expr)) &&
       (isa<ConstantExpr>(arg2Expr)) ) {

    if (bufferGuard) {
      void * ptrIn = (void *) target_ctx_gregs[GREG_RDI].u64;
      size_t sizeIn = (size_t) target_ctx_gregs[GREG_RSI].u64;

      LOG_TASE("Attempting to call realloc with buffer guards enabled\n")
      
      if (ptrIn == NULL) {
	//handle this case like a malloc
	size_t size =  2 + 8 + sizeIn + 8 + 2;
	void * res = malloc(size);
	void * returnedBuf = (void *) ((uint64_t) res + 2 + 8);
	DBG_TASE("bufferGuard obtained mapping on heap at 0x%lx \nbufferGuard returning ptr at 0x%lx \n", (uint64_t) res, (uint64_t) returnedBuf)
	heap_guard_map.insert(std::pair<void *, void *>(returnedBuf, res));

	tase_map_buf((uint64_t) returnedBuf, sizeIn + 6, "realloc return buffer");
	//Poison edges around buffer
	* ((uint16_t *) (res)) = poison_val;
	void * endAddr =(void *)( (uint64_t) res + 2 + 8 + (sizeIn)  + 8);
	*((uint16_t *) (endAddr)) = poison_val;
	ref<ConstantExpr> resultExpr = ConstantExpr::create( (uint64_t) returnedBuf, Expr::Int64);
	target_ctx_gregs_OS->write(GREG_RAX * 8, resultExpr);

	do_ret();//Fake a return
	return;
	
      } else {
	//For the sake of simplicity, just wipe the old mapping and issue a new one.

	size_t size =  2 + 8 + sizeIn + 8 + 2;
	void * res = malloc(size);
	void * returnedBuf = (void *) ((uint64_t) res + 2 + 8);
	//Need to be able to line up returned ptr vs actual buf later when free is called.
	DBG_TASE("bufferGuard obtained mapping on heap at 0x%lx \nbufferGuard returning ptr at 0x%lx \n", (uint64_t) res, (uint64_t) returnedBuf)
	heap_guard_map.insert(std::pair<void *, void *>(returnedBuf, res));

	tase_map_buf((uint64_t) returnedBuf, sizeIn + 6, "realloc return buffer");
	//Poison edges around buffer
	* ((uint16_t *) (res)) = poison_val;
	void * endAddr =(void *)( (uint64_t) res + 2 + 8 + (sizeIn)  + 8);
	*((uint16_t *) (endAddr)) = poison_val;

	//Todo -- copy potentially symbolic data byte-by-byte
	memcpy(returnedBuf, ptrIn, sizeIn);

	//Unbind the old mapping
	void * translatedPtrIn;
	auto lookup = heap_guard_map.find(ptrIn);
	if (lookup != heap_guard_map.end()) {
	  translatedPtrIn = (void *) ((uint64_t) (lookup->second));
	  heap_guard_map.erase(ptrIn);
	} else {
	  //No translation needed
	  translatedPtrIn = ptrIn;
	}

	ObjectPair OP;
	ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) ptrIn, Expr::Int64);
	if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP) ) {
	  const MemoryObject * MO = OP.first;
	  GlobalExecutionStatePtr->addressSpace.unbindObject(MO);
	  free(translatedPtrIn);
	} else {
	  LOG_TASE("Unable to resolve realloc call to underlying buffer in bufferGuard case \n")
	  std::exit(EXIT_FAILURE);
	}

	ref<ConstantExpr> resultExpr = ConstantExpr::create( (uint64_t) returnedBuf, Expr::Int64);
	target_ctx_gregs_OS->write(GREG_RAX * 8, resultExpr);
	do_ret();//Fake a return
	return; 
      
      }
      
      
    } else {
      
      void * ptr = (void *) target_ctx_gregs[GREG_RDI].u64;
      size_t size = (size_t) target_ctx_gregs[GREG_RSI].u64;
      void * res = realloc(ptr,size);
      MOD_TASE("Calling realloc on 0x%lx with size 0x%lx.  Ret val is 0x%lx \n", (uint64_t) ptr, (uint64_t) size, (uint64_t) res)
      if (roundUpHeapAllocations)
	size = roundUp(size, 8);
	
      ref<ConstantExpr> resultExpr = ConstantExpr::create( (uint64_t) res, Expr::Int64);
      target_ctx_gregs_OS->write(GREG_RAX * 8, resultExpr);

      //Treat the realloc(0,size) call like a call to malloc(size)
      if (ptr == NULL) {
	tase_map_buf((uint64_t) res, size, "realloc return buffer");
	
	do_ret();
	return;
      }
	
      if (res != ptr) {
	MOD_TASE("REALLOC call moved site of allocation \n")
	ObjectPair OP;
	ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) ptr, Expr::Int64);
	if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP) ) {
	  const MemoryObject * MO = OP.first;
	  //Todo: carefully copy out/ copy in symbolic data if present
	    
	  GlobalExecutionStatePtr->addressSpace.unbindObject(MO);
	    
	  MemoryObject * newMO = addExternalObject(*GlobalExecutionStatePtr, (void *) res, size, false, "realloc struct");
	  const ObjectState * newOSConst = GlobalExecutionStatePtr->addressSpace.findObject(newMO);
	  ObjectState *newOS = GlobalExecutionStatePtr->addressSpace.getWriteable(newMO,newOSConst);
	  newOS->concreteStore = (uint8_t *) res;
	  MOD_TASE("added MO for realloc at 0x%lx with size 0x%lx after orig location 0x%lx  \n", (uint64_t) res, size, (uint64_t) ptr)
	    
	} else {
	  LOG_TASE("ERROR: realloc called on ptr without underlying buffer \n")
	  LOG_FLUSH()
	  std::exit(EXIT_FAILURE);  
	}
	  
      } else {
	ObjectPair OP;
	ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
	if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP)) {
	  const MemoryObject * MO = OP.first;
	  size_t origObjSize = MO->size;
	  LOG_TASE("REALLOC call kept buffer in same location \n")
	    
	  if (size <= origObjSize) {
	    //Don't need to do anything
	    LOG_TASE("Realloc to smaller or equal size buffer -- no action needed \n")
	  } else {
	    LOG_TASE("Realloc to larger buffer \n")
	    //extend size of MO
	    //Todo: carefully copy out/ copy in symbolic data if present
	    GlobalExecutionStatePtr->addressSpace.unbindObject(MO);
	      
	    MemoryObject * newMO = addExternalObject(*GlobalExecutionStatePtr, (void *) res, size, false, "realloc struct2");
	    const ObjectState * newOSConst = GlobalExecutionStatePtr->addressSpace.findObject(newMO);
	    ObjectState *newOS = GlobalExecutionStatePtr->addressSpace.getWriteable(newMO,newOSConst);
	    newOS->concreteStore = (uint8_t *) res;
	    LOG_TASE("added MO for realloc at 0x%lx with size 0x%lx after orig size 0x%lx  \n", (uint64_t) res, size, origObjSize)
	  }
	} else {
	  LOG_TASE("Error in realloc -- could not find original buffer info for ptr \n")
	  LOG_FLUSH()
	  std::exit(EXIT_FAILURE);
	}
      }
	
      do_ret();//Fake a return
    }
      
  } else {
    concretizeGPRArgs(2, "model_realloc");
    model_realloc();
  }
}

//http://man7.org/linux/man-pages/man3/malloc.3.html

//Todo -- be careful of interaction between sizeArg, initSizeArg, and roundUp.
//Clean that code up so it's simpler.
void Executor::model_malloc() {
  _LOG
  static int times_model_malloc_called = 0;
  times_model_malloc_called++;

  if (isBufferEntirelyConcrete((uint64_t) &(target_ctx_gregs[GREG_RDI].u64), 8)) {
    size_t sizeArg = (size_t) target_ctx_gregs[GREG_RDI].u64;
    DBG_TASE("Entered model_malloc for time %d with requested size 0x%lx \n",times_model_malloc_called, sizeArg)
    
    if (roundUpHeapAllocations) 
      sizeArg = roundUp(sizeArg, 8);

    size_t initSizeArg;
    if (bufferGuard) {
      initSizeArg = sizeArg;
      sizeArg += 20; // 4 bytes for  the psn, plus two 8-byte buffers between psn and the
      //allocated space.  Our poison checking in the compiler sometimes conservatively promotes
      //read/write checks (e.g., an 8 byte write to a 16 byte check) when it can't determine
      //alignment information, so the extra 8-byte buffers should help with that.

      DBG_TASE("Requesting malloc of size 0x%lx for bufferGuard on heap \n",sizeArg)
    }
    void * buf = malloc(sizeArg);

    void * returnedBuf;
    if (bufferGuard) {
      returnedBuf = (void *) ( ((uint64_t) buf) + 2 + 8);
      //Need to be able to line up returned ptr vs actual buf later when free is called.
      DBG_TASE("bufferGuard obtained mapping on heap at 0x%lx \nbufferGuard returning ptr at 0x%lx \n", (uint64_t) buf, (uint64_t) returnedBuf)
      heap_guard_map.insert(std::pair<void *, void *>(returnedBuf, buf));
    }else {
      returnedBuf = buf;
    }

    if (bufferGuard) {
      //Todo -- Should we force-align both the poison buffer and pads to 8 bytes for all, giving
      //a total of 32 bytes of padding?
      tase_map_buf((uint64_t) returnedBuf, initSizeArg +6, "malloc return buffer") ; //6 added to bring us up to alignment
      //Poison edges around buffer
      * ((uint16_t *) (buf)) = poison_val;
      void * endAddr =(void *)( (uint64_t) buf + 2 + 8 + (initSizeArg)  + 8);
      *((uint16_t *) (endAddr)) = poison_val;
    } else {
      tase_map_buf((uint64_t) returnedBuf, sizeArg, "malloc return buffer");
    }
    
    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) returnedBuf, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr); 

    do_ret();//Fake a return
    
    LOG_TASE("INTERPRETER: Exiting model_malloc \n")
  } else {
    concretizeGPRArgs(1, "model_malloc");
    model_malloc();
  }
}

//https://linux.die.net/man/3/free
//Todo -- add check to see if rsp is symbolic, or points to symbolic data (somehow)


void Executor::model_free() {
  _LOG

  static int freeCtr = 0;
  freeCtr++;

  if ( skipFree ) {
    do_ret();
    return;
  }
  
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;
  
  void * freePtr;
  get_val(count, s_offset, __func__, freePtr);

  MOD_TASE("Calling model_free on addr %lx\n", (uint64_t) freePtr)
  if ( bufferGuard ) {
    MOD_TASE("Attempting to free a heap object with buffer guards enabled\n")
	
    auto lookup = heap_guard_map.find(freePtr);
    if (lookup != heap_guard_map.end()) {
      void * translatedAddr = (void *) ((uint64_t) (lookup->second));
      free (translatedAddr);
      heap_guard_map.erase(freePtr);
    } else {  
      free(freePtr);
    }
  } else {
    MOD_TASE("Attempting to free ptr\n")
    free(freePtr);
  }
  MOD_TASE("ptr freed, unbinding object\n")
	   
  ObjectPair OP;
  ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) freePtr, Expr::Int64);
  if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP)) {
    MOD_TASE("object found\n")
    GlobalExecutionStatePtr->addressSpace.unbindObject(OP.first);
    MOD_TASE("object unbound\n")
  } else {
    LOG_TASE("ERROR: Found free called without buffer corresponding to ptr\n")
    std::exit(EXIT_FAILURE);
  }
    
  do_ret();    
}

//
//https://linux.die.net/man/3/freopen
//FILE *freopen(const char *path, const char *mode, FILE *stream);
void Executor::model_freopen() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  char *path;
  char *mode;
  FILE *stream;
  
  get_vals(count, s_offset, __func__, path, mode, stream);

  auto it = std::find_if(open_files.begin(), open_files.end(), [&](FileInfo& x){return x.original_name == path;});
  
  if( it != open_files.end() ) {
    MOD_TASE("calling freopen(0) on handle 0x%lx, file name %s\n", (uint64_t) stream, it->name.c_str())
    
    FILE* res = freopen(it->name.c_str(), mode, stream);
    it->mode = mode;
    it->file = stream;
    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  } else {
    MOD_TASE("calling freopen(1) on handle 0x%lx, file name %s\n", (uint64_t) stream, path)
    FILE* res = freopen(path, mode, stream);
    open_files.push_back({res, path, path, mode, 0});

    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  }
  
  do_ret();//fake a ret
}


//Todo -- check byte-by-byte through the input args for symbolic data
//http://man7.org/linux/man-pages/man3/fopen.3.html
//FILE *fopen(const char *pathname, const char *mode);
void Executor::model_fopen() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr 

  ++s_offset;

  char *pathname;
  char *mode;
  
  get_vals(count, s_offset, __func__, pathname, mode);

  FILE* res = fopen(pathname, mode);
  open_files.push_back(FileInfo{res, pathname, pathname, mode, 0});

  LOG_TASE("Calling fopen on file %s, handle 0x%lx \n", pathname, reinterpret_cast<uint64_t>(res))
  
    //Return result
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();//fake a ret
}

//Todo -- check byte-by-byte through the input args for symbolic data
//http://man7.org/linux/man-pages/man3/fopen.3.html
//FILE *fopen64(const char *pathname, const char *mode);
void Executor::model_fopen64() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  char *pathname;
  char *mode;
  get_vals(count, s_offset, __func__, pathname, mode);

  LOG_TASE("Calling fopen64 on file %s \n", pathname)

  FILE* res = fopen64(pathname, mode);
  open_files.push_back(FileInfo{res, pathname, pathname, mode, 0});
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();//fake a ret
}

//https://linux.die.net/man/3/getc_unlocked
//int getc_unlocked(FILE *stream);
void Executor::model_getc_unlocked() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  FILE* stream;
  get_val(count, s_offset, __func__, stream);

  MOD_TASE("getc unlocked called on handle 0x%lx\n", (uint64_t) stream)
  
  int res = getc_unlocked(stream);
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  
  do_ret();
}  
//   //TODO: Generalize this fast path for all the other models to avoid unnecessary obj
//   //creation.
//   if (isBufferEntirelyConcrete((uint64_t) &target_ctx_gregs[GREG_RDI].u64, 8)
//       && isBufferEntirelyConcrete((uint64_t) &target_ctx_gregs[GREG_RAX].u64, 8)) {
  
  
//     do_ret();
//   } else {
    
//     ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
//     if (isa<ConstantExpr>(arg1Expr)) {
//       int res = getc_unlocked( (FILE *) target_ctx_gregs[GREG_RDI].u64);
      
//       ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
//       target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
//       do_ret();//fake a ret
      
//     } else {
//       concretizeGPRArgs(1, "model_getc_unlocked");
//       model_getc_unlocked();
//     }
    
//   }

// }




//https://www.man7.org/linux/man-pages/man3/feof.3.html
//int feof(FILE *stream);


void Executor::model_feof() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  FILE *stream;
  
  get_vals(count, s_offset, __func__, stream);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) feof(stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();//Fake a return
}

//https://man7.org/linux/man-pages/man3/ferror.3.html
//int ferror(FILE *stream);

void Executor::model_ferror() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  FILE *stream;
  
  get_vals(count, s_offset, __func__, stream);

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) ferror(stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();//Fake a return
}

//https://man7.org/linux/man-pages/man2/posix_fadvise.2.html
//int posix_fadvise(int fd, off_t offset, off_t len, int advice);

void Executor::model_posix_fadvise() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  int fd;
  off_t offset;
  off_t len;
  int advice;
  
  get_vals(count, s_offset, __func__, fd, offset, len, advice);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) posix_fadvise(fd, offset, len, advice), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();  
}

//http://man7.org/linux/man-pages/man3/fclose.3.html
//int fclose(FILE *stream);
//Todo -- examine all bytes of stream for symbolic taint
void Executor::model_fclose() {
  _LOG
    
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  FILE *stream;
  
  get_vals(count, s_offset, __func__, stream);

  open_files.erase(std::remove_if(open_files.begin(), open_files.end(), [&](FileInfo& x){return x.file == stream;}));
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) fclose(stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  
  //We don't need to make any call    
  do_ret();//Fake a return
}

// http://man7.org/linux/man-pages/man3/fseek.3.html
//int fseek(FILE *stream, long offset, int whence);

// Just pass the call through
void Executor::model_fseek() {
  _LOG
      
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr 

  ++s_offset;

  FILE *stream;
  long offset;
  int whence;
  
  get_vals(count, s_offset, __func__, stream, offset, whence);

  //Return result
  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) fseek(stream, offset, whence), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();
}

//http://man7.org/linux/man-pages/man3/ftell.3p.html
// long ftell(FILE *stream);

// Just pass the call through
void Executor::model_ftell() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  FILE *stream;
  
  get_vals(count, s_offset, __func__, stream);

    //Return result
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) ftell(stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();
}


//http://man7.org/linux/man-pages/man3/rewind.3p.html
//void rewind(FILE *stream);

//Just pass the call through
void Executor::model_rewind() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr 

  ++s_offset;

  FILE *stream;
  
  get_vals(count, s_offset, __func__, stream);

  rewind(stream);
  do_ret();  
}

//http://man7.org/linux/man-pages/man3/fread.3.html
//size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
//Todo -- Inspect byte-by-byte for symbolic taint
void Executor::model_fread() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;

  void *ptr;
  size_t size;
  size_t nmemb;
  FILE *stream;

  get_vals(count, s_offset, __func__, ptr, size, nmemb, stream);

  // if( taseDebug > 1 ) {
  //   int x = ftell(stream);
  //   LOG_TASE("testing fread w/ ftell on handle 0x%lx\n", x)
  //   if( x >= 0 ) {
  //     LOG_TASE("offset in file for fread: %d\n", x)
  //   } else {
  //     LOG_TASE("file error in fread/ftell: %d", errno)
  //   }	
  // }
  
  //Return result
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) fread(ptr, size, nmemb, stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();//Fake a return
}

void Executor::model_fread_unlocked() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     
  ++s_offset;

  void *ptr;
  size_t size;
  size_t nmemb;
  FILE *stream;

  get_vals(count, s_offset, __func__, ptr, size, nmemb, stream);
    
  //Return result
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) fread_unlocked(ptr, size, nmemb, stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
  do_ret();//Fake a return
}

 
extern int __isoc99_sscanf ( const char * s, const char * format, ...);
void Executor::model___isoc99_sscanf() {
  _LOG
    
  LOG_TASE("WARNING: Return 0 on unmodeled sscanf call \n")
    
  int res = 0;
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();//Fake a return
  
}


//http://man7.org/linux/man-pages/man3/gethostbyname.3.html
//struct hostent *gethostbyname(const char *name);
//Todo -- check bytes of input for symbolic taint
void Executor::model_gethostbyname() {
  _LOG
    
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  if  (
       (isa<ConstantExpr>(arg1Expr))
       ){
    //Do the call
    LOG_TASE("Calling model_gethostbyname on %s \n", (char *) target_ctx_gregs[GREG_RDI].u64)
    struct hostent * res = (struct hostent *) gethostbyname ((const char *) target_ctx_gregs[GREG_RDI].u64);

    //If it doesn't exit, back hostent struct with a memory object.
    ObjectPair OP;
    ref<ConstantExpr> addrExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    if (GlobalExecutionStatePtr->addressSpace.resolveOne(addrExpr, OP)) {
      LOG_TASE("hostent result appears to have MO already backing it \n")
      
    } else {
      LOG_TASE("Creating MO to back hostent at 0x%lx with size 0x%lx \n", (uint64_t) res, sizeof(hostent))
      MemoryObject * newMO = addExternalObject(*GlobalExecutionStatePtr, (void *) res, sizeof(hostent), false, "gethostbyname struct");
      const ObjectState * newOSConst = GlobalExecutionStatePtr->addressSpace.findObject(newMO);
      ObjectState *newOS = GlobalExecutionStatePtr->addressSpace.getWriteable(newMO,newOSConst);
      newOS->concreteStore = (uint8_t *) res;

      //Also map in h_addr_list elements for now until we get a better way of mapping in env vars and their associated data
      //Todo -get rid of this hack.  For robust environment modeling, we need to find all the pointers-to-pointers and
      //back them with buffers.  We don't currently need that level of modeling just for behavioral verification.
      
      uint64_t  baseAddr = (uint64_t) &(res->h_addr_list[0]);
      size_t size = 0;
      for (char ** itrPtr = res->h_addr_list; *itrPtr != 0; itrPtr++) {
        LOG_TASE("Iterating on h_addr_list \n")
	size++;
      }

      LOG_TASE("h_addr_list has %lu entries \nMapping in buf at 0x%lx\n", size, baseAddr)
      
      MemoryObject * listMO = addExternalObject(*GlobalExecutionStatePtr, (void *) baseAddr, size, false, "gethostbyname struct2");
      const ObjectState * listOSConst = GlobalExecutionStatePtr->addressSpace.findObject(listMO);
      ObjectState * listOS = GlobalExecutionStatePtr->addressSpace.getWriteable(listMO, listOSConst);
      listOS->concreteStore = (uint8_t *) baseAddr;
      
    }

    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
    do_ret();//Fake a return
    
  } else {
    concretizeGPRArgs(1, "model_gethostbyname");
    model_gethostbyname();
  }

}


//int setsockopt(int sockfd, int level, int optname,
//             const void *optval, socklen_t optlen);
//https://linux.die.net/man/2/setsockopt
//Todo -- actually model this
void Executor::model_setsockopt() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     
  ++s_offset;

  int sockfd;
  int level;
  int optname;
  void *optval;
  socklen_t optlen;

  get_vals(count, s_offset, __func__, sockfd, level, optname, optval, optlen);
  
  int res = 0; //Pass success
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  
  do_ret();//Fake a return
}


//No args for this one
void Executor::model___ctype_b_loc() {
  _LOG

  const unsigned short ** constRes = __ctype_b_loc();
  unsigned short ** res = const_cast<unsigned short **>(constRes);
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  
  do_ret();//Fake a return
  
}


//int32_t * * __ctype_tolower_loc(void);
//No args
//Todo -- allocate symbolic underlying results later for testing
void Executor::model___ctype_tolower_loc() {
  _LOG
    
  const int  ** constRes = __ctype_tolower_loc();
  int ** res = const_cast<int **>(constRes);
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  
  do_ret();//Fake a return

}

//int fflush(FILE *stream);
//Todo -- Actually model this or provide a symbolic return status
void Executor::model_fflush(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  FILE* file;
  get_vals(count, s_offset, __func__, file);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) fflush(file), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}


void Executor::model_fflush_unlocked() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  FILE* file;
  get_vals(count, s_offset, __func__, file);

  ref<ConstantExpr> resExpr = ConstantExpr::create((int64_t) fflush_unlocked(file), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}



//char *fgets(char *s, int size, FILE *stream);
//https://linux.die.net/man/3/fgets
void Executor::model_fgets() {
  _LOG
    
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;
  
  char *s;
  int size;
  FILE *stream;
  get_vals(count, s_offset, __func__, s, size, stream);
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) fgets(s, size, stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
}

//Todo -- Inspect byte-by-byte for symbolic taint
// https://linux.die.net/man/3/fwrite
// size_t fwrite(const void *ptr, size_t size, size_t nmemb,
// FILE *stream);
void Executor::model_fwrite() {
  _LOG
  
  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  void *ptr;
  size_t size;
  size_t nmemb;
  FILE *stream;

  get_vals(count, s_offset, __func__, ptr, size, nmemb, stream);

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) fwrite(ptr, size, nmemb, stream), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  do_ret();
} 
 
/*
Executor::print_specifier Executor::parse_specifier (char * input, int * offset) {

  if (input[0] != '%') {
    printf("printf model ERROR: invalid print specifier \n");
    return bad_s;
  }

  if (input[1] == 'd') {
    *offset=2;
    return d_s;
  } else if (input[1] == 'f') {
    *offset=2;
    return f_s;
  } else if (input[1] == 'c') {
    *offset=2;
    return c_s;
  } else if (input[1] == 's') {
    *offset=2;
    return s_s;
  } else if (input[1] == 'l') {
    if (input[2] == 'f') {
      *offset = 3;
      return lf_s;
    } else if (input[2] == 'u') {
      *offset = 3;
      return lu_s;
    } else {
      printf("printf model ERROR: unrecognized print specifier at start of string: \n %s \n", input);
      return bad_s;
    }
  } else {
    printf("printf model ERROR: unrecognized print specifier at start of string: \n %s \n", input);
    return bad_s;
  }

}


//ABI -- RDI, RSI, RDX, RCX, R8, R9 for first integer/ptr args
//For our printf modeling, we're assuming the format string was
//passed into RDI as the 0th arg.  In our limited support for floats
//and doubles, XMM/YMM/ZMM regs are disable so the float/double args
//should go into those general purpose registers.

bool Executor::addPrintfArgNo(std::stringstream * output ,print_specifier type, unsigned int argNo) {
  union BITS {
    uint64_t as_u64;
    int      as_int;
    float    as_float;
    double  as_double;
    char    as_char;
    char * as_str;
  } b;

  switch (argNo){

  case 1 :
    b.as_u64 = target_ctx_gregs[GREG_RSI].u64;
    break;
  case 2:
    b.as_u64 = target_ctx_gregs[GREG_RDX].u64;
    break;
  case 3:
    b.as_u64 = target_ctx_gregs[GREG_RCX].u64;
    break;
  case 4:
    b.as_u64 = target_ctx_gregs[GREG_R8].u64;
    break;
  case 5:
    b.as_u64 = target_ctx_gregs[GREG_R9].u64;
    break;
  default: {
    printf("ERROR: Unable to parse printf arg number %u \n", argNo);
    return false;
  }
  }


  switch (type) {
  case d_s:
    *output << b.as_int;
    break;
  case f_s:
    printf("float arg appears to be %f \n", b.as_float);
    printf("With double spec, float arg appears to be %lf \n", b.as_float);
    printf("As double, arg is %lf \n", b.as_double);
    *output <<b.as_double;
    break;
  case lf_s:
    printf("double arg appears to be %lf \n", b.as_double);
    
    *output << b.as_double;
    break;
  case s_s:
    *output << b.as_str;
    break;
  case c_s:
    *output << b.as_char;
    break;
  case lu_s:
    *output << b.as_u64;
    break;
  default: {
    printf("Error: unrecognized print specifier in model_printf \n");
    return false;
  }
  }

  return true;

}
*/
/*
void Executor::model_printf() {

  char * input = (char *) target_ctx_gregs[GREG_RDI].u64;
  
  unsigned int input_idx = 0;
  size_t len = strlen(input);
  std::stringstream output;

  int currArgNum = 1;

  //Scan through input format string until we hit a %
  while ( input_idx < len) {
    

    if (input[input_idx] == '%') {
      int offset;
      print_specifier ps = parse_specifier((char *) &input[input_idx], &offset);
      if (ps == bad_s) {
	printf("ERROR: Failed to parse format string for printf.  Skipping call. \n");
	do_ret();
	return;
      }

      bool success = addPrintfArgNo(&output, ps, currArgNum);
      if (!success) {
	printf("Encountered error in addPrintfArgNo.  Skipping printf call \n");
	do_ret();
	return;
      }
      currArgNum++;

      input_idx += offset;

    } else {
      output << input[input_idx];

      input_idx++;
    }


  }
  printf("Final result of model_printf----------: \n %s \n", output.str().c_str());
  do_ret();

}
*/
//Modeles for strtod, strtol, etc. and wcstod, wcstol, etc.  These should just
//be user-level code in principal for which we don't need models, but because the musl
//stdlib implmentation reuses some file-based utilities from stdio to handle the string
//manipulation, we're just trapping on these for now to avoid linking in all of stdio.


//Models for strtoX

void Executor::model_strtof() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     

  ++s_offset;

  char * str;
  char ** endptr;

  get_vals(count, s_offset, __func__, str, endptr);

  union BITS {
    float asFloat;
    double asDouble;
    uint64_t asUint64_t;
  } b;

  b.asFloat = strtof(str, endptr);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_strtod() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     

  ++s_offset;

  char * str;
  char ** endptr;

  get_vals(count, s_offset, __func__, str, endptr);
  
  union BITS {
    float asFloat;
    double asDouble;
    uint64_t asUint64_t;
  } b;

  b.asDouble = strtod(str, endptr);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_strtold() {
  LOG_TASE("TASE INFO: Calling strtold and returning 64 bits for long double \n")
  model_strtod();
}


void Executor::model_strtoull() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  char * str;
  char ** endptr;
  int base;

  get_vals(count, s_offset, __func__, str, endptr, base);

  union BITS {
    unsigned long long asULL;
    long long asLL;
    unsigned long asUL;
    long asLong;
    uint64_t asUint64_t;
  } b;
  
  b.asULL = strtoull(str, endptr, base);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
    
}


void Executor::model_strtoll() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  
  ++s_offset;

  char * str;
  char ** endptr;
  int base;

  get_vals(count, s_offset, __func__, str, endptr, base);

  union BITS {
    unsigned long long asULL;
    long long asLL;
    unsigned long asUL;
    long asLong;
    uint64_t asUint64_t;
  } b;
  
  b.asLL = strtoll(str, endptr, base);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_strtoul() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     
  ++s_offset;

  char * str;
  char ** endptr;
  int base;

  get_vals(count, s_offset, __func__, str, endptr, base);

  union BITS {
    unsigned long long asULL;
    long long asLL;
    unsigned long asUL;
    long asLong;
    uint64_t asUint64_t;
  } b;

  b.asUL = strtoul(str, endptr, base);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_strtol() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  
  ++s_offset;

  char *str;
  char **endptr;
  int base;

  get_vals(count, s_offset, __func__, str, endptr, base);

  union BITS {
    unsigned long long asULL;
    long long asLL;
    unsigned long asUL;
    long asLong;
    uint64_t asUint64_t;
  } b;

  b.asLong = strtol(str, endptr, base);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_strtoimax() {
  LOG_TASE("TASE INFO: Modeling strtoimax as strtoll \n")
  model_strtoll();
}
void Executor::model_strtoumax() {
  LOG_TASE("TASE INFO: Modeling strtoumax as strtoull \n")
  model_strtoull();
}

//Models for wcstoX

void Executor::model_wcstof() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     

  ++s_offset;

  wchar_t *nptr;
  wchar_t **endptr;

  get_vals(count, s_offset, __func__, nptr, endptr);
  
  union BITS {
    float asFloat;
    uint64_t asUint64_t;
  } b;
  
  b.asFloat = wcstof(nptr, endptr);
    
  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);    
  do_ret();
}


void Executor::model_wcstod() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr

  ++s_offset;

  wchar_t *nptr;
  wchar_t **endptr;
  
  get_vals(count, s_offset, __func__, nptr, endptr);
  
  union BITS {
    double asDouble;
    uint64_t asUint64_t;
  } b;

  b.asDouble = wcstod(nptr, endptr);
  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_wcstold() {
  LOG_TASE("TASE INFO: Calling model_wctold and returning 64 bits for long double \n")
  model_wcstod();   
}

//wcstol models

void Executor::model_wcstoull() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     

  ++s_offset;

  wchar_t *nptr;
  wchar_t **endptr;
  int base;

  get_vals(count, s_offset, __func__, nptr, endptr, base);

  union BITS {
    unsigned long long asULL;
    uint64_t asUint64_t;
  } b;

  b.asULL = wcstoull(nptr, endptr, base);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_wcstoll() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     
  ++s_offset;

  wchar_t *nptr;
  wchar_t **endptr;
  int base;

  get_vals(count, s_offset, __func__, nptr, endptr, base);

  union BITS {
    long long asLL;
    uint64_t asUint64_t;
  } b;

  b.asLL = wcstoll(nptr, endptr, base);

  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();

}


void Executor::model_wcstoul() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
                                                                                                                                              
  ++s_offset;

  wchar_t *nptr;
  wchar_t **endptr;
  int base;

  get_vals(count, s_offset, __func__, nptr, endptr, base);

  union BITS {
    unsigned long asUL;
    uint64_t asUint64_t;
  } b;

  b.asUL = wcstoul(nptr, endptr, base);
  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
}


void Executor::model_wcstol() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr  
  ++s_offset;

  wchar_t *nptr;
  wchar_t **endptr;
  int base;

  get_vals(count, s_offset, __func__, nptr, endptr, base);

  union BITS {
    long asLong;
    uint64_t asUint64_t;
  } b;

  b.asLong = wcstol(nptr, endptr, base);
  
  ref<ConstantExpr> resExpr = ConstantExpr::create(b.asUint64_t, Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}


void Executor::model_wcstoimax() {
  LOG_TASE("TASE INFO: Modeling wcstoimax as wcstoll \n")
  model_wcstoll();
}
void Executor::model_wcstoumax() {
  LOG_TASE("TASE INFO: Modeling wcstoumax as wcstoull \n")
  model_wcstoull();
}

// size_t mbsrtowcs (wchar_t* dest, const char** src, size_t max, mbstate_t* ps);
void Executor::model_mbsrtowcs(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr
  ++s_offset;


  wchar_t* dest;
  const char** src;
  size_t max;
  mbstate_t* ps;
  get_vals(count, s_offset, __func__, dest, src, max, ps);

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) mbsrtowcs(dest, src, max, ps), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}
// just mapping in in initialization instead...
// Executor::model_getprogname(){
//   tase_map_buf((uint64_t) &program_invocation_short_name, strlen(program_invocation_short_name));
//   ref<ConstantExpr> res = ConstantExpr::create((uint64_t) &program_invocation_short_name[0], Expr::Int64);
//   tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
//   do_ret();
// }

void Executor::model_puts() {
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64; // RSP should be sitting on return addr                                     
  ++s_offset;

  char* str;
  get_val(count, s_offset, __func__, str);

  LOG_TASE("model_puts called with str \"%s\"\n", str);
  
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) puts(str), Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}



void Executor::model_setlocale(){
  _LOG

  int count = 0;
  uint64_t * s_offset = (uint64_t*) target_ctx_gregs[GREG_RSP].u64;
  ++s_offset;

  int category;
  char * locale;
  get_vals(count, s_offset, __func__, category, locale);

  char * out = setlocale(category, locale);
  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) out, Expr::Int64);
  tase_helper_write((uint64_t) &target_ctx_gregs[GREG_RAX], resExpr);
  do_ret();
}

//We're not fully modeling sprintf just yet because of varargs.  However, some sub-libraries
// we do support in musl (e.g., stdlib, ctype, string) have dependencies on sprintf.
//So as a workaround, we cherry-pick those specific calls for now and otherwise
//return an error noting that the function isn't modeled yet.

//The specific calls we're cherry-picking now are ecvt, fcvt, and gcvt in stdlib.
//Todo: Be careful when using this for SSL verification.
/*
void Executor::model_sprintf() {

  char * str = (char *) target_ctx_gregs[GREG_RDI].u64;
  char * fmt = (char *) target_ctx_gregs[GREG_RSI].u64;

  union BITS {
    uint64_t asuint64_t;
    double asdouble;
  } arg4;
  arg4.asuint64_t = target_ctx_gregs[GREG_RCX].u64;
  
  if        (strcmp(fmt, "%.*e") == 0 ) { 
    sprintf(str, fmt, target_ctx_gregs[GREG_RDX].i32, arg4.asdouble);
  } else if (strcmp(fmt, "%.*f") == 0 ) {
    sprintf(str, fmt, target_ctx_gregs[GREG_RDX].i32, arg4.asdouble);
  } else if (strcmp(fmt, "%.*g") == 0 ) {
    sprintf(str, fmt, target_ctx_gregs[GREG_RDX].i32, arg4.asdouble);
  } else {
    printf("ERROR: Unmodeled sprintf call in TASE \n");
    worker_exit();
  }

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) strlen(str), Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
  
  do_ret();
  
}
*/
//This struct comes from pthread_impl.h in musl.
struct pthread {
  /* Part 1 -- these fields may be external or
   * internal (accessed via asm) ABI. Do not change. */
  struct pthread *self;
  uintptr_t *dtv;
  struct pthread *prev, *next; /* non-ABI */
  uintptr_t sysinfo;
  uintptr_t canary, canary2;

  /* Part 2 -- implementation details, non-ABI. */
  int tid;
  int errno_val;
  volatile int detach_state;
  volatile int cancel;
  volatile unsigned char canceldisable, cancelasync;
  unsigned char tsd_used:1;
  unsigned char dlerror_flag:1;
  unsigned char *map_base;
  size_t map_size;
  void *stack;
  size_t stack_size;
  size_t guard_size;
  void *result;
  void *cancelbuf;
  void **tsd;
  struct {
    volatile void *volatile head;
    long off;
    volatile void *volatile pending;
  } robust_list;
  volatile int timer_id;
  void * locale;
  volatile int killlock[1];
  char *dlerror_buf;
  void *stdio_locks;

  /* Part 3 -- the positions of these fields relative to
   * the end of the structure is external and internal ABI. */
  uintptr_t canary_at_end;
  uintptr_t *dtv_copy;
};

//Handle calls to __pthread_self from our subset of musl libc.  We just
//set up a dummy pthread struct with the entire thing (including the
//errno field) set to 0.

//This is something we'd flesh out if we want to
//do more environment modeling; should be OK for now as-is because
//our subset of libc only uses this pthread struct for accessing errno.
struct pthread * dummy_pthread_struct;
void Executor::model___pthread_self() {
  _LOG
  static int pthread_self_calls = 0;
  if (pthread_self_calls == 0) {
    dummy_pthread_struct = (struct pthread *) calloc(sizeof( struct pthread), 1);
    tase_map_buf( (uint64_t) dummy_pthread_struct, sizeof( struct pthread), "dummy pthread struct");
    LOG_TASE("TASE INFO: Initializing dummy pthread struct for target \n")
  } else {
    LOG_TASE("TASE INFO: Returning dummy pthread struct in call to __pthread_self \n")
  }

  ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) dummy_pthread_struct, Expr::Int64);
  target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

  do_ret();
  
}

//Implementation for a_ctz_64 and a_clz_64 comes directly from internal/atomic.h in musl.
//We're just trapping on these for now because the emitted code for them
//use bsr and bsl instructions, which aren't implemented in TASE yet.
/*
void Executor::model_a_ctz_64() {
  static const char debruijn64[64] = {
				      0, 1, 2, 53, 3, 7, 54, 27, 4, 38, 41, 8, 34, 55, 48, 28,
				      62, 5, 39, 46, 44, 42, 22, 9, 24, 35, 59, 56, 49, 18, 29, 11,
				      63, 52, 6, 26, 37, 40, 33, 47, 61, 45, 43, 21, 23, 58, 17, 10,
				      51, 25, 36, 32, 60, 20, 57, 16, 50, 31, 19, 15, 30, 14, 13, 12
  };

  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  if  (
       (isa<ConstantExpr>(arg1Expr))
       ){
    
    uint64_t x = target_ctx_gregs[GREG_RDI].u64;
    
    int res =  debruijn64[(x&-x)*0x022fdd63cc95386dull >> 58];
    
    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);
    
    do_ret();
    
  } else {
    concretizeGPRArgs(1, "model_a_ctz_64");
    model_a_ctz_64();
  }
}


void Executor::model_a_clz_64() {
  ref<Expr> arg1Expr = target_ctx_gregs_OS->read(GREG_RDI * 8, Expr::Int64);
  if  (
       (isa<ConstantExpr>(arg1Expr)) 
       ){

    uint64_t x = target_ctx_gregs[GREG_RDI].u64;
    
    uint32_t y;
    int r;
    if (x>>32) y=x>>32, r=0; else y=x, r=32;
    if (y>>16) y>>=16; else r |= 16;
    if (y>>8) y>>=8; else r |= 8;
    if (y>>4) y>>=4; else r |= 4;
    if (y>>2) y>>=2; else r |= 2;
    int res =  r | !(y>>1);

    ref<ConstantExpr> resExpr = ConstantExpr::create((uint64_t) res, Expr::Int64);
    target_ctx_gregs_OS->write(GREG_RAX * 8, resExpr);

    do_ret();

  } else {
    concretizeGPRArgs(1, "model_a_clz_64");
    model_a_clz_64();
  }
}
*/
