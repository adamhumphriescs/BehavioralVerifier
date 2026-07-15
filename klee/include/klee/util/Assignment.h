//===-- Assignment.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_UTIL_ASSIGNMENT_H
#define KLEE_UTIL_ASSIGNMENT_H

#include <map>

#include "klee/util/ExprEvaluator.h"
#include "tase_interp.h"
extern bool inModelPCS;
// FIXME: Rename?

namespace klee {
  class Array;

  class Assignment {
  public:
    typedef std::map<const Array*, std::vector<unsigned char> > bindings_ty;

    bool allowFreeValues;
    bindings_ty bindings;
    
  public:
    Assignment(bool _allowFreeValues=false) 
      : allowFreeValues(_allowFreeValues) {}
    Assignment(const std::vector<const Array*> &objects,
               std::vector< std::vector<unsigned char> > &values,
               bool _allowFreeValues=false) 
      : allowFreeValues(_allowFreeValues){
      std::vector< std::vector<unsigned char> >::iterator valIt = 
        values.begin();
      for (std::vector<const Array*>::const_iterator it = objects.begin(),
             ie = objects.end(); it != ie; ++it) {
        const Array *os = *it;
        std::vector<unsigned char> &arr = *valIt;
        bindings.insert(std::make_pair(os, arr));
        ++valIt;
      }
    }
    
    ref<Expr> evaluate(const Array *mo, unsigned index) const;
    ref<Expr> evaluate(ref<Expr> e);
    void createConstraintsFromAssignment(std::vector<ref<Expr> > &out) const;

    template<typename InputIterator>
    bool satisfies(InputIterator begin, InputIterator end);
    void dump();
  };
  
  class AssignmentEvaluator : public ExprEvaluator {
    const Assignment &a;

  protected:
    ref<Expr> getInitialValue(const Array &mo, unsigned index) {
      //LOG_TASE("In AssignmentEvaluator getInitialValue \n");LOG_FLUSH();
      return a.evaluate(&mo, index);
    }
    
  public:
    AssignmentEvaluator(const Assignment &_a) : a(_a) {}    
  };

  /***/

  inline ref<Expr> Assignment::evaluate(const Array *array, 
                                        unsigned index) const {
    //LOG_TASE("In assignment.h evaluate \n");LOG_FLUSH();
    assert(array);
    //LOG_TASE("Array name  is   %s \n", array->name.c_str()); LOG_FLUSH();
    //LOG_TASE("Bindings has size %d \n", bindings.size());LOG_FLUSH();

    bindings_ty::const_iterator it = bindings.find(array);
    //LOG_TASE("eval dbg 1 \n");LOG_FLUSH();
    if (it!=bindings.end() && index<it->second.size()) {
      //LOG_TASE("eval dbg 2 \n");LOG_FLUSH();
      return ConstantExpr::alloc(it->second[index], array->getRange());
    } else {
      //LOG_TASE("eval dbg 3 \n");LOG_FLUSH();
      if (allowFreeValues) {
        return ReadExpr::create(UpdateList(array, 0), 
                                ConstantExpr::alloc(index, array->getDomain()));
      } else {
        return ConstantExpr::alloc(0, array->getRange());
      }
    }
  }

  inline ref<Expr> Assignment::evaluate(ref<Expr> e) { 
    if (inModelPCS) {
      //LOG_TASE("In Assignment evaluate \n");LOG_FLUSH();
    }
    AssignmentEvaluator v(*this);
    if (inModelPCS) {
      //LOG_TASE("DBG 1c \n");LOG_FLUSH();
    }
    //New for dbg
    ref<Expr> tmp = v.visit(e);
    if (inModelPCS) {
      //LOG_TASE("DBG 2c \n");LOG_FLUSH();
    }
    return tmp;
    //return v.visit(e); 
  }

  template<typename InputIterator>
  inline bool Assignment::satisfies(InputIterator begin, InputIterator end) {
    AssignmentEvaluator v(*this);
    for (; begin!=end; ++begin)
      if (!v.visit(*begin)->isTrue())
        return false;
    return true;
  }
}

#endif
