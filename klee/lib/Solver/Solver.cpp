//===-- Solver.cpp --------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/Constraints.h"
#include "klee/Internal/System/Time.h"
#include "tase_interp.h"

extern int taseDebug;
using namespace klee;

const char *Solver::validity_to_str(Validity v) {
  switch (v) {
  default:    return "Unknown";
  case True:  return "True";
  case False: return "False";
  }
}

Solver::~Solver() { 
  delete impl; 
}

char *Solver::getConstraintLog(const Query& query) {
    return impl->getConstraintLog(query);
}

void Solver::setCoreSolverTimeout(double timeout) {
    impl->setCoreSolverTimeout(timeout);
}

bool Solver::evaluate(const Query& query, Validity &result) {
  if (taseDebug > 0)
    LOG_TASE("evaluate called\n");
  LOG_TASE("In generic evaluate \n");LOG_FLUSH();
  assert(query.expr->getWidth() == Expr::Bool && "Invalid expression type!");
  LOG_TASE("CALLING GENERIC EVALUATE IN SOLVER.CPP \n");LOG_FLUSH();
  // Maintain invariants implementations expect.
  double T0 = util::getWallTime();
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(query.expr)) {
    result = CE->isTrue() ? True : False;
    return true;
  }
  //return impl->computeValidity(query, result);
  bool res = impl->computeValidity(query, result);
  LOG_TASE("GENERIFC SOLVER: Spent %lf seconds in total in evaluate \n", util::getWallTime() - T0);LOG_FLUSH();
  return res;
}

bool Solver::evaluateCheat(const Query& query, Validity &result) {
  assert(query.expr->getWidth() == Expr::Bool && "Invalid expression type!");
  if (taseDebug > 0){
    LOG_TASE("Calling evaluateCheat \n");
    LOG_FLUSH();
  }
  
  // Maintain invariants implementations expect.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(query.expr)) {
    result = CE->isTrue() ? True : False;
    return true;
  }

  return impl->computeValidityCheat(query, result);
}


bool Solver::mustBeTrue(const Query& query, bool &result) {
  if (taseDebug > 0) 
    LOG_TASE("mustBeTrue called\n");
  assert(query.expr->getWidth() == Expr::Bool && "Invalid expression type!");

  // Maintain invariants implementations expect.
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(query.expr)) {
    result = CE->isTrue() ? true : false;
    return true;
  }

  return impl->computeTruth(query, result);
}

bool Solver::mustBeFalse(const Query& query, bool &result) {
  return mustBeTrue(query.negateExpr(), result);
}

bool Solver::mayBeTrue(const Query& query, bool &result) {
  if (taseDebug > 0)
    LOG_TASE("mayBeTrue called\n");
  bool res;
  if (!mustBeFalse(query, res))
    return false;
  result = !res;
  return true;
}

bool Solver::mayBeFalse(const Query& query, bool &result) {
  if(taseDebug > 0) 
    LOG_TASE("mayBeFalse called\n");
  bool res;
  if (!mustBeTrue(query, res))
    return false;
  result = !res;
  return true;
}

bool Solver::getValue(const Query& query, ref<ConstantExpr> &result) {
  // Maintain invariants implementation expect.
  LOG_TASE("In generic getValue \n");LOG_FLUSH();
  if (taseDebug > 0) 
    LOG_TASE("getValue called\n");
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(query.expr)) {
    result = CE;
    return true;
  }

  // FIXME: Push ConstantExpr requirement down.
  ref<Expr> tmp;
  if (!impl->computeValue(query, tmp))
    return false;
  LOG_TASE("Returning from generic getValue \n");LOG_FLUSH();
  result = cast<ConstantExpr>(tmp);
  return true;
}

bool 
Solver::getInitialValues(const Query& query,
                         const std::vector<const Array*> &objects,
                         std::vector< std::vector<unsigned char> > &values) {
  if (taseDebug > 0) 
    LOG_TASE("getInitialValues called\n");
  bool hasSolution;
  bool success =
    impl->computeInitialValues(query, objects, values, hasSolution);
  // FIXME: Propogate this out.
  if (!hasSolution) {
    LOG_TASE("Doesn't have solution \n");
    LOG_FLUSH();
    return false;
  }
  return success;
}

std::pair< ref<Expr>, ref<Expr> > Solver::getRange(const Query& query) {
  ref<Expr> e = query.expr;
  Expr::Width width = e->getWidth();
  uint64_t min, max;

  if (width==1) {
    Solver::Validity result;
    if (!evaluate(query, result))
      assert(0 && "computeValidity failed");
    switch (result) {
    case Solver::True: 
      min = max = 1; break;
    case Solver::False: 
      min = max = 0; break;
    default:
      min = 0, max = 1; break;
    }
  } else if (ConstantExpr *CE = dyn_cast<ConstantExpr>(e)) {
    min = max = CE->getZExtValue();
  } else {
    // binary search for # of useful bits
    uint64_t lo=0, hi=width, mid, bits=0;
    while (lo<hi) {
      mid = lo + (hi - lo)/2;
      bool res;
      bool success = 
        mustBeTrue(query.withExpr(
                     EqExpr::create(LShrExpr::create(e,
                                                     ConstantExpr::create(mid, 
                                                                          width)),
                                    ConstantExpr::create(0, width))),
                   res);

      assert(success && "FIXME: Unhandled solver failure");
      (void) success;

      if (res) {
        hi = mid;
      } else {
        lo = mid+1;
      }

      bits = lo;
    }
    
    // could binary search for training zeros and offset
    // min max but unlikely to be very useful

    // check common case
    bool res = false;
    bool success = 
      mayBeTrue(query.withExpr(EqExpr::create(e, ConstantExpr::create(0, 
                                                                      width))), 
                res);

    assert(success && "FIXME: Unhandled solver failure");      
    (void) success;

    if (res) {
      min = 0;
    } else {
      // binary search for min
      lo=0, hi=bits64::maxValueOfNBits(bits);
      while (lo<hi) {
        mid = lo + (hi - lo)/2;
        bool res = false;
        bool success = 
          mayBeTrue(query.withExpr(UleExpr::create(e, 
                                                   ConstantExpr::create(mid, 
                                                                        width))),
                    res);

        assert(success && "FIXME: Unhandled solver failure");      
        (void) success;

        if (res) {
          hi = mid;
        } else {
          lo = mid+1;
        }
      }

      min = lo;
    }

    // binary search for max
    lo=min, hi=bits64::maxValueOfNBits(bits);
    while (lo<hi) {
      mid = lo + (hi - lo)/2;
      bool res;
      bool success = 
        mustBeTrue(query.withExpr(UleExpr::create(e, 
                                                  ConstantExpr::create(mid, 
                                                                       width))),
                   res);

      assert(success && "FIXME: Unhandled solver failure");      
      (void) success;

      if (res) {
        hi = mid;
      } else {
        lo = mid+1;
      }
    }

    max = lo;
  }

  return std::make_pair(ConstantExpr::create(min, width),
                        ConstantExpr::create(max, width));
}

void Query::dump() const {
  llvm::errs() << "Constraints [\n";
  for (ConstraintManager::const_iterator i = constraints.begin();
      i != constraints.end(); i++) {
    (*i)->dump();
  }
  llvm::errs() << "]\n";
  llvm::errs() << "Query [\n";
  expr->dump();
  llvm::errs() << "]\n";
}
