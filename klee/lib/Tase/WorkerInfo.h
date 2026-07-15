#ifndef WORKERINFO_H
#define WORKERINFO_H

struct WorkerInfo {
  pid_t pid;
  pid_t originator;
  size_t branches;
  double priority;
  void* pinfo; // ptr into shared memory buffer
};


#endif
