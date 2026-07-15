#include <queue>
#include <algorithm>
#include "WorkerInfo.h"

extern void wait_killed(pid_t pid);

enum WorkerGroup_t {
		    STACK,
		    QUEUE,
		    PQ
};



struct MLPQGreaterThan {
  bool operator() (struct WorkerInfo  left, struct WorkerInfo right) {
    return left.priority < right.priority;
  }
};
    // double leftPriority = left.priority;
    // double rightPriority = right.priority;
    //We should add a min priority queue implementation for edit distance.  For now,
    //we'll remove the range restrictions on priority and make it work for edit distance.
    /*
    if (leftPriority < 0 || leftPriority > 1 || rightPriority < 0 || rightPriority > 1) {
      printf("ERROR: priority is out of range \n");
      fflush(stdout);
      exit(1);
      } else*/
  //    return (leftPriority < rightPriority);
  //  }
//};

struct WorkerGroup {
  std::priority_queue<struct WorkerInfo , std::vector<struct WorkerInfo>, MLPQGreaterThan> pq;
  // now we're just using make_heap/push_heap/pop_heap etc from algorithm library to implement heap operations
  // on top of our deque
  std::deque<struct WorkerInfo> dq;
  enum WorkerGroup_t type;
  
  //Destructively get the "best"  (e.g., highest priority for PQ or first in for BFS) worker
  
  WorkerInfo pop() {
    WorkerInfo best;
    if (type == PQ) {
      best = pq.top();
      pq.pop();
    } else if (type == QUEUE) {
      best = dq.front();
      dq.pop_front();
    } else if (type == STACK) {
      best = dq.back();
      dq.pop_back();
    } else {
      LOG_TASE("Unspecified worker group type in pop \n");LOG_FLUSH();
      exit(0);
    }
    return best;
  }



  /*
  WorkerInfo pop() {
    WorkerInfo best;
    if( type == PQ ) {
      best = dq.front();
      dq.pop_front();
      //      pop_heap(dq.begin(), dq.end(), MLPQGreaterThan{});
      
    } else {
      if( klee::explorationType == TASEExplorationType::BFS ) {
	best = dq.front();
	dq.pop_front();
	make_heap(dq.begin(), dq.end(), MLPQGreaterThan{});  
	
      } else {
	best = dq.back();
	dq.pop_back();
      }
    }
    return best;
    } */

  void push(WorkerInfo w) {
    if (type == PQ) {
      pq.push(w);
    } else {
      dq.push_back(w); //For both stack and queue, push to the "back"
    }
  }

  /*
  void push(WorkerInfo w) {
    dq.push_back(w);
    
    if( type == PQ ){
      push_heap(dq.begin(), dq.end(), MLPQGreaterThan{});
    }
    }*/
  
  bool empty() {
    if (type == PQ) {
      return pq.empty();
    } else {
      return dq.empty();
    }
  }

  /*
  bool empty() {
    return dq.empty();
    }*/

  size_t size() {
    if (type == PQ) {
      return pq.size();
    } else {
      return dq.size();
    }
  }
  /*
  size_t size() {
    return dq.size();
    }*/

  void cleanUp() {
    if (type ==PQ) {
      while (!pq.empty()) {
	struct WorkerInfo curr = pq.top();
	pq.pop();
	if (curr.pid != -1) {
	  //printf("Attempting to kill pid %d \n", curr.pid);fflush(stdout);
	  kill(curr.pid, SIGKILL);
	  //wait_killed(curr.pid);
	  //printf("Killed pid %d \n", curr.pid);fflush(stdout);
	}
      }
    } else {
      while ( !dq.empty()) {
	struct WorkerInfo curr = dq.back();
	dq.pop_back();
	if (curr.pid != -1) {
	  //printf("Attempting to kill pid %d \n", curr.pid);fflush(stdout);
	  kill(curr.pid, SIGKILL);
	  //wait_killed(curr.pid);
	  //printf("Killed pid %d \n", curr.pid);fflush(stdout);
	}
      }
    }
  }

/*
  void cleanUp() {
    if ( type == PQ ) {
      while ( !dq.empty()) {
	struct WorkerInfo curr = dq.front();
	dq.pop_front();
	pop_heap(dq.begin(), dq.end(), MLPQGreaterThan{});
	
	printf("Attempting to kill pid %d \n", curr.pid);fflush(stdout);
	kill(curr.pid, SIGKILL);
	wait_killed(curr.pid);
	printf("Killed pid %d \n", curr.pid);fflush(stdout);
      }
    } else {
      while ( !dq.empty()) {
	struct WorkerInfo curr = dq.back();
	dq.pop_back();
	printf("Attempting to kill pid %d \n", curr.pid);fflush(stdout);
	kill(curr.pid, SIGKILL);
	wait_killed(curr.pid);
	printf("Killed pid %d \n", curr.pid);fflush(stdout);
      }
    }
    }*/

  bool find(WorkerInfo * r, pid_t pid) {
    if (type == PQ) {
      LOG_TASE("ERROR: Find not supported for PQ\n"); LOG_FLUSH();
      exit(0);
      return false;
    } else {
      for(auto x = dq.begin(); x != dq.end(); x++) {
	if( x->pid == pid ) {
	  *r = *x;
	  return true;
	}
      }
      return false;
    }
  }
  
  /*
  bool find(WorkerInfo * r, pid_t pid) {
    for(auto x = dq.begin(); x != dq.end(); x++) {
      if( x->pid == pid ) {
     *r = *x;
     return true;
      }
    }
    return false;
  }
  */
  // destructive find
  bool get(WorkerInfo * r, pid_t pid) {
    if (type == PQ) {
      LOG_TASE("ERROR: Get not supported for PQ\n");LOG_FLUSH();
      exit(0);
      return false;
    } else {
      for(auto x = dq.begin(); x != dq.end(); x++) {
	if( x->pid == pid ) {
	  *r = *x;
	  dq.erase(x);
	  make_heap(dq.begin(), dq.end(), MLPQGreaterThan{});
	  return true;
	}
      }
      return false;
    }

  }
  /*
  // destructive find
  bool get(WorkerInfo * r, pid_t pid) {
    for(auto x = dq.begin(); x != dq.end(); x++) {
      if( x->pid == pid ) {
     *r = *x;
     dq.erase(x);
     make_heap(dq.begin(), dq.end(), MLPQGreaterThan{});     
     return true;
      }
    }
    return false;
  }
  */
  WorkerGroup(WorkerGroup_t type)
    : dq(), pq()
    , type(type)
  {}

  ~WorkerGroup(){cleanUp();}
  };


// struct WorkerGroupDeque {
//   typedef void(*finish_t)(std::deque<WorkerInfo>&);
//   std::deque<WorkerInfo> workers;
//   finish_t cleanup;
//   WorkerInfo popf() {
//     auto x = workers.front();
//     workers.pop_front();
//     return x;
//   }
//   WorkerInfo popb() {
//     auto x = workers.back();
//     workers.pop_back();
//     return x;
//   }
//   void push(const WorkerInfo& w) {
//     workers.push_back(w);
//   }
//   bool find(WorkerInfo * r, pid_t pid) {
//     for(auto x = workers.begin(); x != workers.end(); x++) {
//       if( x->pid == pid ) {
// 	*r = *x;
// 	return true;
//       }
//     }
//     return false;
//   }
//   // destructive find
//   bool get(WorkerInfo * r, pid_t pid) {
//     for(auto x = workers.begin(); x != workers.end(); x++) {
//       if( x->pid == pid ) {
// 	*r = *x;
// 	workers.erase(x);
// 	return true;
//       }
//     }

//     return false;
//   }
//   size_t size() {
//     return workers.size();
//   }
//   bool empty() {
//     return workers.empty();
//   }
//   void clear() {
//     workers.clear();
//   }
//   void cleanUp() {

//   }
  
// };

// struct WorkerGroup {
//   struct WorkerGroupDeque *dequeImpl;
//   struct WorkerGroupPQ  *PQImpl;
//   enum WorkerGroup_t type;

  
  // void initDeque() {
  //   type = DEQUE;
  // }

  // void initPQ() {
  //   type = PQ;
  // }
  
  // WorkerInfo popf() {
  //   if (type == DEQUE) {
  //     return dequeImpl.popf();
  //   } else {
  //     printf("Unsupported operation popf for WorkerGroup type \n");fflush(stdout); exit(0); 
  //   }
  // }
  // WorkerInfo popb() {
  //   if (type == DEQUE) {
  //     return dequeImpl.popb();
  //   } else {
  //     printf("Unsupported operation popb for WorkerGroup type \n");fflush(stdout); exit(0);
  //   }
  // }
    
//   void push(const WorkerInfo& w) {
//     if (type == DEQUE) {
//       dequeImpl.push(w);
//     } else {
//       printf("Unsupported operation push for WorkerGroup type \n");fflush(stdout); exit(0);
//     }
//   }

//   bool find(WorkerInfo * r, pid_t pid) {
//     if (type == DEQUE) {
//       return dequeImpl.find(r,pid);
//     } else {
//       printf("Unsupported operation find for WorkerGroup type \n");fflush(stdout); exit(0); 
//     }
//   }

//   // destructive find
//   bool get(WorkerInfo * r, pid_t pid) {
//     if (type == DEQUE) {
//       return dequeImpl.get(r,pid);
//     } else {
//       printf("Unsupported operation get for WorkerGroup type \n");fflush(stdout); exit(0); 
//     }
//   }

//   size_t size() {
//     if (type == DEQUE) {
//       return dequeImpl.size();
//     } else if (type == PQ) {
//       return PQImpl.size();
//     } else {
//       printf("Unsupported operation size for WorkerGroup type \n");fflush(stdout); exit(0); 
//     }
//   }
  
//   bool empty() {
//     if (type == DEQUE) {
//       return dequeImpl.empty();
//     } else if (type == PQ) {
//       return PQImpl.empty();
//     } else {
//       printf("Unsupported operation empty for WorkerGroup type \n");fflush(stdout); exit(0);
//     }
    
//   }
//   struct WorkerInfo getBest() {
//     if (type == DEQUE) {
//       printf("Unsupported operation getBest for WorkerGroup type \n");fflush(stdout); exit(0); 
//     } else if (type == PQ) {
//       return PQImpl.getBest();
//     } else {
//       printf("Unsupported operation getBest for WorkerGroup type \n");fflush(stdout); exit(0); 
//     }
//   }

//   void add(WorkerInfo w) {
//     if (type == DEQUE) {
//       printf("Unsupported operation add for WorkerGroup type \n");fflush(stdout); exit(0);
//     } else if (type == PQ) {
//       PQImpl.add(w);
//     } else {
//       printf("Unsupported operation add for WorkerGroup type \n");fflush(stdout); exit(0);
//     }
//   }

//   void cleanUp() {
//     if (type == DEQUE) {
//       dequeImpl.cleanUp();
//     } else if (type == PQ) {
//       PQImpl.cleanUp();
//     } else {
//       printf("Unsupported operation cleanUp for WorkerGroup type \n");fflush(stdout); exit(0);
//     }
//   }
  
// };


