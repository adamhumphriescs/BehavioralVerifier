#define _GNU_SOURCE 1
#include <deque>
#include <algorithm>
#include <memory>
#include <cstring>
#include <sys/prctl.h>
#include <sys/mman.h>

#include "API_Scout.h"
#include "klee/CommandLine.h"
#include "WorkerInfo.h"
#include "tase_interp.h"
#include "WorkerGroup.h"

//extern bool taseDebug;
//extern bool modelDebug;
extern target_ctx_t target_ctx;
extern FILE * prev_stdout_log;

// standard signal types
enum class SIGNALS {
		    ABORT,
		    SUCCESS,
		    ERROR,
		    FORK_REQUEST
};

extern size_t MAX_RUNNING_WORKERS;
extern size_t MAX_STOPPED_WORKERS;

// worker_fork is intended to be called by workers
// all other items from the API are just for the managing process to call

// originator is the process that was cloned, but we use CLONE_PARENT in clone3 to reparent to the manager process
// struct WorkerInfo {
//   pid_t pid;
//   pid_t originator;
//   size_t branches;
//   bool scout;  // useful for debug
// };

extern "C" void renew_fds();
extern uint64_t getMLBBID (uint64_t rip);
// worker_fork is intended to be called by workers
// all other items from the API are just for the managing process to call

// originator is the process that was cloned, but we use CLONE_PARENT in clone3 to reparent to the manager process
// pid/originator/branches only updated on fork. priority only set/used within manager, irrelevant for client
// struct WorkerInfo {
//   pid_t pid;
//   pid_t originator;
//   size_t branches;
//   double priority;
//   bool scout;  // useful for debug
//   void* pinfo; // ptr into shared memory buffer
// };

WorkerInfo workerInfo;



extern int pinfo_bytes; // client-defined size for pinfo struct

void* info_cache;
int cache_size;
uint64_t slots;

// client-defined items:
extern "C" {
void predict(WorkerInfo* winfo); // uses WorkerInfo items to make prediction, update priorities and info struct
void copy_worker_info(); // copy info struct into shared memory from local struct
void retrieve_worker_info(); // copy info struct from shared memory to local struct
void update_worker_info(uint64_t i);
void init_oracle();
}
void sigcont_handler(int sig, siginfo_t *info, void *ucontext) {
  workerInfo.pinfo = info->si_ptr;
}


void sigsegv_handler(int sig, siginfo_t *info, void *ucontext) {
  sigval x;
  //  x.sival_ptr = reinterpret_cast<void*>(target_ctx.rip.u64);
  LOG_TASE("mcontext RIP: %llx\ncontext RIP: %lx\n", reinterpret_cast<ucontext_t*>(ucontext)->uc_mcontext.gregs[GREG_RIP], target_ctx.rip.u64);
  LOG_FLUSH();
  x.sival_ptr = reinterpret_cast<void*>(reinterpret_cast<ucontext_t*>(ucontext)->uc_mcontext.gregs[GREG_RIP]);
  sigqueue(manager_pid, SEGV, x);
  abort();
}

// size pinfo_bytes is constant per-program
// set in API user's code
void alloc_in_cache(void *&pinfo) {
  int slot_size = pinfo_bytes % 8 == 0 ? pinfo_bytes / 8 : pinfo_bytes / 8 + 1;
  for( int x = 0; x < cache_size / (slot_size*8); x++ ) {
    if( (slots & (0x1<<x)) == 0 ) {
      slots |= (0x1<<x);
      pinfo = (void*) (((uint8_t*) info_cache) + x*slot_size);
      return;
    }
  }

  LOG_TASE("info_cache space exceeded!\n");
  LOG_FLUSH();
    
  exit(1);  
}


void dealloc_in_cache(void* pinfo) {
  int slot_size = pinfo_bytes % 8 == 0 ? pinfo_bytes / 8 : pinfo_bytes / 8 + 1;
  int slot = (((uint8_t*) pinfo) - ((uint8_t*) info_cache)) / slot_size;
  slots ^= (0x1<<slot);
}


void worker_cleanup(std::deque<WorkerInfo>& workers);


extern WorkerGroup * Stopped;
extern WorkerGroup * Running;
pid_t manager_pid;
extern pid_t backup;
extern pid_t scout;
extern uint64_t scout_counter;
int sfd;
struct signalfd_siginfo signals[MAX_EVENTS];
int num_signals;
bool success = false;
bool tase_error = false;

#define WAITFLAGS WUNTRACED | __WCLONE
//#define WAITFLAGS WUNTRACED

// wait could be interrupted and fail, so keep in the loop
// bool wait_stopped(pid_t pid) {
//   while( true ) {
//     int status;
//     //    LOG_TASE("wait_stopped %d\n", pid);
//     //    LOG_FLUSH();
//     int ret = waitpid(pid, &status, WAITFLAGS );
//     if( ret == -1 ) {
//       if( ( errno == ECHILD || errno == ESRCH ) )
// 	//	continue;
//         return true;

//       LOG_TASE("Error in wait_stopped: pid %d, errno: %d\n", pid, errno);
//       LOG_FLUSH();
//       return false;
//     }
    
//     if( ret > 0 && WIFSTOPPED(status) )
//       return true;
//   }
// }

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
// bool wait_killed(pid_t pid) {
//   while( true ) {
//     int status;    
//     //    LOG_TASE("wait_killed %d\n", pid);
//     //    LOG_FLUSH();
//     int ret = waitpid(pid, &status, WAITFLAGS );
//     if( ret == -1 && ( errno == ECHILD || errno == ESRCH ) )
//       return false;
    
//     if( ret > 0 && ( WIFEXITED(status) || WIFSIGNALED(status) ) )
//       return true;
//   }
// }

bool wait_started(pid_t pid, sigval x) {
  sigqueue(pid, SIGCONT, x);
  
  while( true ) {
    int status;
    //    LOG_TASE("wait_started %d\n", pid);
    //    LOG_FLUSH();    
    int ret = waitpid(pid, &status, WAITFLAGS | WCONTINUED );
    if( ret == -1 && ( errno == ECHILD || errno == ESRCH ) )
      return false;
	
    if( ret > 0 && WIFCONTINUED(status) )
      return true;
  }
}


void deathsig() {
  if( getpid() != manager_pid ) {
    sigval x;

    LOG_TASE("pid %d death signal. Scout: %d, backup: %d, counter: %lu, RIP: %lx\n", getpid(), scout, backup, scout_counter, target_ctx.rip.u64);
    LOG_FLUSH();
    
    if( scout == 0 ) {
      if( scout_counter > 0 ) {
	x.sival_int = scout_counter;
	sigqueue(backup, SIGSTD, x);
      }

      x.sival_int = success ? 0 : -1; // 0 on success -> no scout signal -> no extra forking
      sigqueue(backup, SIGSTD, x);    // scout signaling the backup on exit
    }

    if( !success && klee::verTestType != VerTestType::SINGLEMSGVER && klee::verTestType != VerTestType::VERIFY ) {
      x.sival_int = static_cast<int>(SIGNALS::ABORT);
      sigqueue(manager_pid, SIGSTD, x); // abort signal to manager
    }
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
  DBG_TASE("Creating shared mem %d bytes, %d bytes per slot, %ld slots\n", cache_size, pinfo_bytes, MAX_RUNNING_WORKERS);
  int fd = -1;
  info_cache = mmap(NULL, cache_size, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_ANONYMOUS, fd, 0);

  if( info_cache == (void*) -1 ) {
    LOG_TASE("Error during mmap\n");
    LOG_FLUSH();
    exit(1);
  }

  
  if( MAX_RUNNING_WORKERS % 2 != 0 ) // need even number for scout processes
    MAX_RUNNING_WORKERS+=1;
  
  manager_pid = getpid();

  prctl(PR_SET_CHILD_SUBREAPER, 1);
  
  sigset_t mask;
  
  sigemptyset(&mask);
  sigaddset(&mask, SIGSTD);   // standard signals
  sigaddset(&mask, SIGSCOUT); // scout signal
  sigaddset(&mask, SEGV);     // segmentation fault
  
  if( sigprocmask(SIG_BLOCK, &mask, NULL) == - 1 ) {
    LOG_TASE("Could not set sigprocmask\n");
    LOG_FLUSH();
    exit(1);
  }

  sigemptyset(&mask);
  sigaddset(&mask, SIGSTD);   // standard signals
  sigaddset(&mask, SIGSCOUT); // scout signal       
  sigaddset(&mask, SEGV);     // segmentation fault
  
  sfd = signalfd(-1, &mask, 0);
  if( sfd == -1 ) {
    LOG_TASE("Error creating signalfd\n");
    LOG_FLUSH();
    exit(1);
  }

  struct sigaction sa;
  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGCONT);
  sa.sa_sigaction = sigcont_handler;
  sigaction(SIGCONT, &sa, NULL);

  sa.sa_sigaction = sigsegv_handler;

  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGSEGV);
  sigaction(SIGSEGV, &sa, NULL);

  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGBUS);  
  sigaction(SIGBUS, &sa, NULL);

  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGTRAP);  
  sigaction(SIGTRAP, &sa, NULL);

  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGFPE);  
  sigaction(SIGFPE, &sa, NULL);

  sigemptyset(&sa.sa_mask);
  sigaddset(&sa.sa_mask, SIGILL);  
  sigaction(SIGILL, &sa, NULL);
	    
  
  atexit(deathsig);
}


void destroy_structures(WorkerGroup ** Stopped, WorkerGroup ** Running) {
  // auto destroy = [](WorkerInfo& x){ kill(x.pid, SIGKILL); wait_killed(x.pid);};
  // std::for_each((*Stopped)->begin(), (*Stopped)->end(), destroy);
  // std::for_each((*Running)->begin(), (*Running)->end(), destroy);
  // (*Stopped)->clear();
  // (*Running)->clear();

  (*Running)->cleanUp();
  (*Stopped)->cleanUp();
  munmap(info_cache, cache_size);  
}


// kill the worker processess and wait on them
void worker_cleanup(std::deque<WorkerInfo>& workers) {
  std::for_each(workers.begin(), workers.end(), [](WorkerInfo& w){
 						  kill(w.pid, SIGKILL);
						  wait_killed(w.pid);
						});
}



int schedule_worker(WorkerGroup * Stopped, WorkerGroup * Running) {
  if ( Running->size() < MAX_RUNNING_WORKERS ) {
    WorkerInfo tmp = Stopped->pop();
    alloc_in_cache(tmp.pinfo);

    DBG_TASE("Scheduling worker %d to run\n", tmp.pid);
    LOG_FLUSH();
    Running->push( tmp );

    sigval x;
    x.sival_ptr = tmp.pinfo;
    if( ! wait_started(tmp.pid, x) ) {
      LOG_TASE("Error starting worker\n");
      LOG_FLUSH();
      destroy_structures(&Stopped, &Running);
      exit(1);
    }
    
    return 1;
  }
  
  return 0;
}


// fork replacement but with reparenting to calling process's parent to allow manager to wait
pid_t call_fork() {
  struct clone_args args = {};
  args.flags = CLONE_PARENT|CLONE_PTRACE;
  return (pid_t) syscall(SYS_clone3, &args, sizeof(struct clone_args));
}


// We don't use Stopped/Running here since they are only actually available in
// the manager process and not shared mem for this implementation
// but the API has them here
pid_t worker_fork(WorkerGroup * Stopped, WorkerGroup * Running) {
  copy_worker_info();

  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::FORK_REQUEST);
  sigqueue(manager_pid, SIGSTD, x);

  kill(getpid(), SIGSTOP);

  retrieve_worker_info(); // get updated info. Priority is wrong in local struct, but we don't use it there!

  pid_t child = call_fork();
  if( child == -1 ) {
    LOG_TASE("Fork failed\n")
    LOG_FLUSH()
    destroy_structures(&Stopped, &Running);
    exit(1);
  }

  if( child != 0 ) {
    sigval x;
    x.sival_int = *reinterpret_cast<int*>(&child);  // pid_t isn't int but same size
    sigqueue(manager_pid, SIGSTD, x);
  } else {
    renew_fds();
    kill(getpid(), SIGSTOP);
  }

  copy_worker_info();
  return child;
}


pid_t initial_fork() {
  struct clone_args args = {};
  pid_t pid = (pid_t) syscall(SYS_clone3, &args, sizeof(struct clone_args));

  if( pid == -1 ) {
    LOG_TASE("Fork failed\n")
    LOG_FLUSH()
    destroy_structures(&Stopped, &Running);
    exit(1);
  }
  
  if( pid != 0 ) {
    LOG_TASE("Initial worker forked\n");
    LOG_FLUSH();
    Stopped->push(WorkerInfo{pid, getpid(), 0, -1, NULL}); // add initial worker
    wait_stopped(pid);
  } else {    
    kill(getpid(), SIGSTOP);
  }

  return pid;
}



void fetch_signals(WorkerGroup * Stopped, WorkerGroup * Running) {
  int bytes = read( sfd, signals, sizeof(struct signalfd_siginfo) * MAX_EVENTS );
  if ( bytes == 0 ) {
    num_signals = 0;
    return;
  } else if ( bytes == -1 ) {
    LOG_TASE("Error reading events\n")
    LOG_FLUSH()
    destroy_structures(&Stopped, &Running);
    exit(1);
  }

  num_signals = bytes / sizeof(struct signalfd_siginfo);
}


void clear_signals() {
  memset(&signals[0], '\0', MAX_EVENTS*sizeof(struct signalfd_siginfo));
}


// where the magic happens
void handle_signals(WorkerGroup * Stopped, WorkerGroup * Running) {
  fetch_signals(Stopped, Running);

  // handle sigsegv/abort/success/error first
  WorkerInfo tmp;
  WorkerInfo tmp2;
  sigval x;
    
  for( int i = 0; i < num_signals; i++ ) {
    if( signals[i].ssi_signo == SEGV ) {
      LOG_TASE("SIGSEGV in process %d, addr %lx\n", signals[i].ssi_pid, reinterpret_cast<uint64_t>(signals[i].ssi_ptr))
      LOG_FLUSH()
      destroy_structures(&Stopped, &Running);
      tase_error = true;
      return;
      
    } else if( signals[i].ssi_signo == SIGSTD ) { // standard signals
      switch( SIGNALS(signals[i].ssi_int) ) {
      case SIGNALS::ABORT:  // scout abort signal also sent to backup on exit, no special case here. Handled in tase/src/tase/common_scout.c
	Running->get(&tmp, signals[i].ssi_pid) || Stopped->get(&tmp, signals[i].ssi_pid);


	DBG_TASE("Signal: Abort, pid %d\n", signals[i].ssi_pid);
	LOG_FLUSH();
	dealloc_in_cache(tmp.pinfo);
	
	wait_killed(signals[i].ssi_pid);
	break;
	
      case SIGNALS::SUCCESS: // print something here...
	DBG_TASE("Signal: Success, pid %d\n", signals[i].ssi_pid);
	LOG_FLUSH();

	destroy_structures(&Stopped, &Running);
	success = true;
	
	return; // ignore remaining signals

      case SIGNALS::ERROR:
	LOG_TASE("Signal: Worker Error, pid %d\nShutting down.\n", signals[i].ssi_pid);
	LOG_FLUSH();

	destroy_structures(&Stopped, &Running);
	tase_error = true;
	
	return; // ignore remaining signals
      case SIGNALS::FORK_REQUEST: // handled elsewhere
	break;
      }
    }
  }
  
  for( int i = 0; i < num_signals; i++ ) {
    if( signals[i].ssi_signo == SIGSTD ) { // standard signals

      switch( SIGNALS(signals[i].ssi_int) ) {
      case SIGNALS::ABORT:
      case SIGNALS::SUCCESS:
      case SIGNALS::ERROR:
	continue; // skip these, handled above

      case SIGNALS::FORK_REQUEST:
	Running->get(&tmp, signals[i].ssi_pid); // destructive-find
	predict(&tmp);                          // updated in-place
	Running->push( tmp );                   // add back altered WorkerInfo
	x.sival_ptr = tmp.pinfo;                // send new pinfo ptr, probably same as old one
	if ( !wait_started(tmp.pid, x) ) {
	  LOG_TASE("Error  in FORK_REQUEST: pid %d DOA, removing from queue\n", tmp.pid);
	  LOG_FLUSH();
	  Running->get( &tmp, signals[i].ssi_pid );
	}
	break;
	
      default: // fork
	DBG_TASE("Signal: Fork, pid %d\n", signals[i].ssi_pid);
	LOG_FLUSH();
	
	if( Stopped->size() == MAX_STOPPED_WORKERS ) {
	  LOG_TASE("MAX_STOPPED_WORKERS Exceeded. Execution failed\n");
	  LOG_FLUSH();
	  destroy_structures(&Stopped, &Running);
	  exit(1);
	}

	Running->find(&tmp, signals[i].ssi_pid);// || Stopped->find(&tmp, signals[i].ssi_pid); 
	tmp2 = {*reinterpret_cast<pid_t*>(&signals[i].ssi_int), (pid_t)signals[i].ssi_pid, tmp.branches+1, -1, NULL};
	Stopped->push(tmp2);

	wait_stopped(tmp.pid);
	wait_stopped(*reinterpret_cast<pid_t*>(&signals[i].ssi_int));
	break;
      }
      
    } else if ( signals[i].ssi_signo == SIGSCOUT ) {
      DBG_TASE("Signal: Scout Fork, pid %d\n", signals[i].ssi_pid);
      LOG_FLUSH();

      // scout fork. Scout goes into Running. Sent by originator == new scout, contains new backup's PID.
      // corresponding code for the forking is in tase/src/tase/common_scout.c
      // should set 'pid_t scout' to be the scout process ID in the new backup process,
      // and 0 in the new scout process.
      
      pid_t scout_pid = signals[i].ssi_pid;
      pid_t backup_pid = *reinterpret_cast<pid_t*>(&signals[i].ssi_int);
            
      Running->get(&tmp, scout_pid); // || Stopped->get(&tmp, scout_pid);
      //      tmp.scout = true; // backup becomes new scout
      tmp2 = {backup_pid, scout_pid, tmp.branches, -1, NULL};
      
      if( Running->size()+1 < MAX_RUNNING_WORKERS ){
	Running->push(tmp);
	
	alloc_in_cache(tmp2.pinfo);
	Running->push(tmp2);

	wait_stopped(scout_pid);
	x.sival_ptr = tmp.pinfo;
	if( !wait_started(scout_pid, x) ) {
	  LOG_TASE("Error in Scout Fork: scout process (pid %d) DOA, removing from queue\n", scout_pid);
	  LOG_FLUSH();
	  Running->get(&tmp, scout_pid);
	}
	
	wait_stopped(backup_pid);
	x.sival_ptr = tmp2.pinfo;
	if( !wait_started(backup_pid, x) ) {
	  LOG_TASE("Error in Scout Fork: backup process (pid %d) DOA, removing from queue\n", backup_pid);
	  LOG_FLUSH();
	  Running->get(&tmp, backup_pid);
	}
	// need to copy pinfo in backup process before scout fork signal.
	// scout and backup will have identical local pinfo structs if done before the fork call in scout
	// and it means we don't need special handling before the dealloc_in_cache two lines down from here
      } else if( Stopped->size()+1 < MAX_STOPPED_WORKERS ) {
	dealloc_in_cache(tmp.pinfo);
        Stopped->push(tmp);
	Stopped->push(tmp2);
	wait_stopped(scout_pid);
	wait_stopped(backup_pid);
	
      } else {
	LOG_TASE("%s Exceeded. Execution failed.\n", Running->size()+1 >= MAX_RUNNING_WORKERS ? "MAX_RUNNING_WORKERS" : "MAX_STOPPED_WORKERS");
	LOG_FLUSH();
	destroy_structures(&Stopped, &Running);
	exit(1);
      }
    }
  }
  LOG_FLUSH()  
  clear_signals();
}


void manage_workers() {
  while( (!success && !tase_error) || !Stopped->empty() || !Running->empty() ) {

    while( !Stopped->empty() && schedule_worker(Stopped, Running) ){}

    handle_signals(Stopped, Running);
  }
  
  LOG_TASE("All workers finished.\n");
  LOG_FLUSH();
  
  delete Stopped;
  delete Running;
}



void worker_success(WorkerGroup * Stopped, WorkerGroup * Running) {
  LOG_FLUSH();
  fflush(prev_stdout_log);
  
  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::SUCCESS);
  sigqueue(manager_pid, SIGSTD, x);
}


void worker_error(WorkerGroup *Stopped, WorkerGroup *Running) {
  LOG_FLUSH();
  fflush(prev_stdout_log);
  
  sigval x;
  x.sival_int = static_cast<int>(SIGNALS::ERROR);
  sigqueue(manager_pid, SIGSTD, x);
}


int tase_fork_RIP(std::vector<uint64_t> dests) {
  MOD_TASE("PID %d Calling regular tase_fork_RIP \n", getpid());

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

  return dests.size()-1;
}


int tase_fork_IR(uint64_t trueBranchID, uint64_t falseBranchID) {
  MOD_TASE("PID %d calling tase_forkIR_PQ with branch IDs %ld and %ld \n", getpid(), trueBranchID, falseBranchID); 
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


//------------------------------------------------
#include <sys/sem.h>
#include <iostream>
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
  DBG_TASE("Calling getNewMLID \n");
  get_sem_lock();
  *MLIDPtr = *MLIDPtr + 1;
  int val = *MLIDPtr;


  release_sem_lock();
  DBG_TASE("Called getNewMLID \n"); 
  return val;
}

