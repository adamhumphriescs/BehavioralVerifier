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
//#include "../../../test/tase/include/tase/tase_interp.h"
//#include "../../../test/tase/include/tase/tase_shims.h"
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

extern std::map<double, std::vector<float>> CurrBBEncodingMap;

std::vector<int> BBBowVec;
void initBBBowVec() {
  printf("Calling initBBBowVec \n");fflush(stdout);

  for (unsigned int i = 0; i < CurrBBEncodingMap.size(); i++) {
    BBBowVec.push_back(0);
  }
}

void reset_BBBOW_Vec() {
  for (unsigned int i = 0; i < BBBowVec.size(); i++) {
    BBBowVec[i] = 0;
  }
}


//Slightly modified bag of words constraint representation from LEARCH.
//https://files.sri.inf.ethz.ch/website/papers/ccs21-learch.pdf

std::vector<double> constraint_features(32, 0.0);  //All path constraints since beginning of verification
std::vector<double> round_constraint_features(32, 0.0);  //Constraints from trying to verify current message

void Executor::addConstraintBOW(ref<Expr> expr, std::vector<double>& features) {
  assert(features.size() == 32);
  switch(expr->getKind()) {
  case Expr::Constant:
    features[0] += 1;
    break;
  case Expr::NotOptimized:
    features[1] += 1;
    addConstraintBOW(cast<NotOptimizedExpr>(expr)->src, features);
    break;
  case Expr::Read:
    features[2] += 1;
    addConstraintBOW(cast<ReadExpr>(expr)->index, features);
    break;
  case Expr::Select:
    features[3] += 1;
    addConstraintBOW(cast<SelectExpr>(expr)->cond, features);
    addConstraintBOW(cast<SelectExpr>(expr)->trueExpr, features);
    addConstraintBOW(cast<SelectExpr>(expr)->falseExpr, features);
    break;
  case Expr::Concat:
    features[4] += 1;
    addConstraintBOW(cast<ConcatExpr>(expr)->getLeft(), features);
    addConstraintBOW(cast<ConcatExpr>(expr)->getRight(), features);
    break;
  case Expr::Extract:
    features[5] += 1;
    addConstraintBOW(cast<ExtractExpr>(expr)->expr, features);
    break;
  case Expr::ZExt:
    features[6] += 1;
    addConstraintBOW(cast<ZExtExpr>(expr)->src, features);
    break;
  case Expr::SExt:
    features[7] += 1;
    addConstraintBOW(cast<SExtExpr>(expr)->src, features);
    break;
  case Expr::Not:
    features[8] += 1;
    addConstraintBOW(cast<NotExpr>(expr)->expr, features);
    break;
  case Expr::Add:
    features[9] += 1;
    addConstraintBOW(cast<AddExpr>(expr)->left, features);
    addConstraintBOW(cast<AddExpr>(expr)->right, features);
    break;
  case Expr::Sub:
    features[10] += 1;
    addConstraintBOW(cast<SubExpr>(expr)->left, features);
    addConstraintBOW(cast<SubExpr>(expr)->right, features);
    break;
  case Expr::Mul:
    features[11] += 1;
    addConstraintBOW(cast<MulExpr>(expr)->left, features);
    addConstraintBOW(cast<MulExpr>(expr)->right, features);
    break;
  case Expr::UDiv:
    features[12] += 1;
    addConstraintBOW(cast<UDivExpr>(expr)->left, features);
    addConstraintBOW(cast<UDivExpr>(expr)->right, features);
    break;
  case Expr::SDiv:
    features[13] += 1;
    addConstraintBOW(cast<SDivExpr>(expr)->left, features);
    addConstraintBOW(cast<SDivExpr>(expr)->right, features);
    break;
  case Expr::URem:
    features[14] += 1;
    addConstraintBOW(cast<URemExpr>(expr)->left, features);
    addConstraintBOW(cast<URemExpr>(expr)->right, features);
    break;
  case Expr::SRem:
    features[15] += 1;
    addConstraintBOW(cast<SRemExpr>(expr)->left, features);
    addConstraintBOW(cast<SRemExpr>(expr)->right, features);
    break;
  case Expr::And:
    features[16] += 1;
    addConstraintBOW(cast<AndExpr>(expr)->left, features);
    addConstraintBOW(cast<AndExpr>(expr)->right, features);
    break;
  case Expr::Or:
    features[17] += 1;
    addConstraintBOW(cast<OrExpr>(expr)->left, features);
    addConstraintBOW(cast<OrExpr>(expr)->right, features);
    break;
  case Expr::Xor:
    features[18] += 1;
    addConstraintBOW(cast<XorExpr>(expr)->left, features);
    addConstraintBOW(cast<XorExpr>(expr)->right, features);
    break;
  case Expr::Shl:
    features[19] += 1;
    addConstraintBOW(cast<ShlExpr>(expr)->left, features);
    addConstraintBOW(cast<ShlExpr>(expr)->right, features);
    break;
  case Expr::LShr:
    features[20] += 1;
    addConstraintBOW(cast<LShrExpr>(expr)->left, features);
    addConstraintBOW(cast<LShrExpr>(expr)->right, features);
    break;
  case Expr::AShr:
    features[21] += 1;
    addConstraintBOW(cast<AShrExpr>(expr)->left, features);
    addConstraintBOW(cast<AShrExpr>(expr)->right, features);
    break;
  case Expr::Eq:
    features[22] += 1;
    addConstraintBOW(cast<EqExpr>(expr)->left, features);
    addConstraintBOW(cast<EqExpr>(expr)->right, features);
    break;
  case Expr::Ne:
    features[23] += 1;
    addConstraintBOW(cast<NeExpr>(expr)->left, features);
    addConstraintBOW(cast<NeExpr>(expr)->right, features);
    break;
  case Expr::Ult:
    features[24] += 1;
    addConstraintBOW(cast<UltExpr>(expr)->left, features);
    addConstraintBOW(cast<UltExpr>(expr)->right, features);
    break;
  case Expr::Ule:
    features[25] += 1;
    addConstraintBOW(cast<UleExpr>(expr)->left, features);
    addConstraintBOW(cast<UleExpr>(expr)->right, features);
    break;
  case Expr::Ugt:
    features[26] += 1;
    addConstraintBOW(cast<UgtExpr>(expr)->left, features);
    addConstraintBOW(cast<UgtExpr>(expr)->right, features);
    break;
  case Expr::Uge:
    features[27] += 1;
    addConstraintBOW(cast<UgeExpr>(expr)->left, features);
    addConstraintBOW(cast<UgeExpr>(expr)->right, features);
    break;
  case Expr::Slt:
    features[28] += 1;
    addConstraintBOW(cast<SltExpr>(expr)->left, features);
    addConstraintBOW(cast<SltExpr>(expr)->right, features);
    break;
  case Expr::Sle:
    features[29] += 1;
    addConstraintBOW(cast<SleExpr>(expr)->left, features);
    addConstraintBOW(cast<SleExpr>(expr)->right, features);
    break;
  case Expr::Sgt:
    features[30] += 1;
    addConstraintBOW(cast<SgtExpr>(expr)->left, features);
    addConstraintBOW(cast<SgtExpr>(expr)->right, features);
    break;
  case Expr::Sge:
    features[31] += 1;
    addConstraintBOW(cast<SgeExpr>(expr)->left, features);
    addConstraintBOW(cast<SgeExpr>(expr)->right, features);
    break;
  default:
    break;
  }
}

void Executor::remConstraintBOW(ref<Expr> expr, std::vector<double>& features) {
  assert(features.size() == 32);
  switch(expr->getKind()) {
  case Expr::Constant:
    features[0] -= 1;
    break;
  case Expr::NotOptimized:
    features[1] -= 1;
    remConstraintBOW(cast<NotOptimizedExpr>(expr)->src, features);
    break;
  case Expr::Read:
    features[2] -= 1;
    remConstraintBOW(cast<ReadExpr>(expr)->index, features);
    break;
  case Expr::Select:
    features[3] -= 1;
    remConstraintBOW(cast<SelectExpr>(expr)->cond, features);
    remConstraintBOW(cast<SelectExpr>(expr)->trueExpr, features);
    remConstraintBOW(cast<SelectExpr>(expr)->falseExpr, features);
    break;
  case Expr::Concat:
    features[4] -= 1;
    remConstraintBOW(cast<ConcatExpr>(expr)->getLeft(), features);
    remConstraintBOW(cast<ConcatExpr>(expr)->getRight(), features);
    break;
  case Expr::Extract:
    features[5] -= 1;
    remConstraintBOW(cast<ExtractExpr>(expr)->expr, features);
    break;
  case Expr::ZExt:
    features[6] -= 1;
    remConstraintBOW(cast<ZExtExpr>(expr)->src, features);
    break;
  case Expr::SExt:
    features[7] -= 1;
    remConstraintBOW(cast<SExtExpr>(expr)->src, features);
    break;
  case Expr::Not:
    features[8] -= 1;
    remConstraintBOW(cast<NotExpr>(expr)->expr, features);
    break;
  case Expr::Add:
    features[9] -= 1;
    remConstraintBOW(cast<AddExpr>(expr)->left, features);
    remConstraintBOW(cast<AddExpr>(expr)->right, features);
    break;
  case Expr::Sub:
    features[10] -= 1;
    remConstraintBOW(cast<SubExpr>(expr)->left, features);
    remConstraintBOW(cast<SubExpr>(expr)->right, features);
    break;
  case Expr::Mul:
    features[11] -= 1;
    remConstraintBOW(cast<MulExpr>(expr)->left, features);
    remConstraintBOW(cast<MulExpr>(expr)->right, features);
    break;
  case Expr::UDiv:
    features[12] -= 1;
    remConstraintBOW(cast<UDivExpr>(expr)->left, features);
    remConstraintBOW(cast<UDivExpr>(expr)->right, features);
    break;
  case Expr::SDiv:
    features[13] -= 1;
    remConstraintBOW(cast<SDivExpr>(expr)->left, features);
    remConstraintBOW(cast<SDivExpr>(expr)->right, features);
    break;
  case Expr::URem:
    features[14] -= 1;
    remConstraintBOW(cast<URemExpr>(expr)->left, features);
    remConstraintBOW(cast<URemExpr>(expr)->right, features);
    break;
  case Expr::SRem:
    features[15] -= 1;
    remConstraintBOW(cast<SRemExpr>(expr)->left, features);
    remConstraintBOW(cast<SRemExpr>(expr)->right, features);
    break;
  case Expr::And:
    features[16] -= 1;
    remConstraintBOW(cast<AndExpr>(expr)->left, features);
    remConstraintBOW(cast<AndExpr>(expr)->right, features);
    break;
  case Expr::Or:
    features[17] -= 1;
    remConstraintBOW(cast<OrExpr>(expr)->left, features);
    remConstraintBOW(cast<OrExpr>(expr)->right, features);
    break;
  case Expr::Xor:
    features[18] -= 1;
    remConstraintBOW(cast<XorExpr>(expr)->left, features);
    remConstraintBOW(cast<XorExpr>(expr)->right, features);
    break;
  case Expr::Shl:
    features[19] -= 1;
    remConstraintBOW(cast<ShlExpr>(expr)->left, features);
    remConstraintBOW(cast<ShlExpr>(expr)->right, features);
    break;
  case Expr::LShr:
    features[20] -= 1;
    remConstraintBOW(cast<LShrExpr>(expr)->left, features);
    remConstraintBOW(cast<LShrExpr>(expr)->right, features);
    break;
  case Expr::AShr:
    features[21] -= 1;
    remConstraintBOW(cast<AShrExpr>(expr)->left, features);
    remConstraintBOW(cast<AShrExpr>(expr)->right, features);
    break;
  case Expr::Eq:
    features[22] -= 1;
    remConstraintBOW(cast<EqExpr>(expr)->left, features);
    remConstraintBOW(cast<EqExpr>(expr)->right, features);
    break;
  case Expr::Ne:
    features[23] -= 1;
    remConstraintBOW(cast<NeExpr>(expr)->left, features);
    remConstraintBOW(cast<NeExpr>(expr)->right, features);
    break;
  case Expr::Ult:
    features[24] -= 1;
    remConstraintBOW(cast<UltExpr>(expr)->left, features);
    remConstraintBOW(cast<UltExpr>(expr)->right, features);
    break;
  case Expr::Ule:
    features[25] -= 1;
    remConstraintBOW(cast<UleExpr>(expr)->left, features);
    remConstraintBOW(cast<UleExpr>(expr)->right, features);
    break;
  case Expr::Ugt:
    features[26] -= 1;
    remConstraintBOW(cast<UgtExpr>(expr)->left, features);
    remConstraintBOW(cast<UgtExpr>(expr)->right, features);
    break;
  case Expr::Uge:
    features[27] -= 1;
    remConstraintBOW(cast<UgeExpr>(expr)->left, features);
    remConstraintBOW(cast<UgeExpr>(expr)->right, features);
    break;
  case Expr::Slt:
    features[28] -= 1;
    remConstraintBOW(cast<SltExpr>(expr)->left, features);
    remConstraintBOW(cast<SltExpr>(expr)->right, features);
    break;
  case Expr::Sle:
    features[29] -= 1;
    remConstraintBOW(cast<SleExpr>(expr)->left, features);
    remConstraintBOW(cast<SleExpr>(expr)->right, features);
    break;
  case Expr::Sgt:
    features[30] -= 1;
    remConstraintBOW(cast<SgtExpr>(expr)->left, features);
    remConstraintBOW(cast<SgtExpr>(expr)->right, features);
    break;
  case Expr::Sge:
    features[31] -= 1;
    remConstraintBOW(cast<SgeExpr>(expr)->left, features);
    remConstraintBOW(cast<SgeExpr>(expr)->right, features);
    break;
  default:
    break;
  }
}

void reset_round_constraint_features() {
  for (unsigned int i = 0; i < round_constraint_features.size(); i++) {
    round_constraint_features[i] = 0.0;
  }
}

void Executor::addConstraintFeature(ref <Expr> e) {
  addConstraintBOW(e, constraint_features);
  addConstraintBOW(e, round_constraint_features);
}

void Executor::remConstraintFeature(ref <Expr> e) {
  remConstraintBOW(e, constraint_features);
  remConstraintBOW(e, round_constraint_features);
}

