//===-- EditDistance.h ------------------------------------------*- C++ -*-===//
//
// <insert license>
//
//===----------------------------------------------------------------------===//
//
//===----------------------------------------------------------------------===//
#ifndef CLIVER_EDITDISTANCH_H
#define CLIVER_EDITDISTANCH_H

#include <algorithm>
#include <cmath>
#include <iostream>
#include <map>
#include <stack>
#include <vector>

#include <assert.h>
#include <limits.h>
#include "stdint.h"

namespace cliver {

enum { MATCH=0, INSERT, DELETE };

template<class SequenceType, class ElementType, class ValueType,
         int MatchCost=1, int DeleteCost=1, int InsertCost=1>
class Score {
 public:
  static inline ValueType match(const SequenceType &s1, const SequenceType &s2, 
                         unsigned pos1, unsigned pos2) {
    return match(s1[pos1], s2[pos2]);
  }

  static inline ValueType insert(const SequenceType &s1, const SequenceType &s2, 
                          unsigned pos1, unsigned pos2) {
    return InsertCost;
  }

  static inline ValueType del(const SequenceType &s1, const SequenceType &s2, 
                       unsigned pos1, unsigned pos2) {
    return DeleteCost;
  }

  static inline ValueType match(const SequenceType &s1, const ElementType &e2, 
                         unsigned pos1) {
    return match(s1[pos1], e2);
  }

  static inline ValueType insert(const SequenceType &s1, const ElementType &e2, 
                          unsigned pos1) {
    return InsertCost;
  }

  static inline ValueType del(const SequenceType &s1, const ElementType &e2, 
                       unsigned pos1) {
    return DeleteCost;
  }

  static inline ValueType match(const ElementType &e1, const SequenceType &s2, 
                         unsigned pos2) {
    return match(e1, s2[pos2]);
  }

  static inline ValueType insert(const ElementType &e1, const SequenceType &s2, 
                          unsigned pos2) {
    return InsertCost;
  }

  static inline ValueType del(const ElementType &e1, const SequenceType &s2, 
                       unsigned pos2) {
    return DeleteCost;
  }

  static inline ValueType match(const ElementType &e1, const ElementType &e2) {
    if (e1 == e2) return 0;
    return MatchCost;
  }

  static inline ValueType insert(const ElementType &e1, const ElementType &e2) {
    return InsertCost;
  }

  static inline ValueType del(const ElementType &e1, const ElementType &e2) {
    return DeleteCost;
  }
};

template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceTable {
 public:
  EditDistanceTable(const SequenceType &s, const SequenceType &t) 
   : s_(s),
     t_(t),
     m_(s_.size()+1), 
     n_(t_.size()+1),
     costs_(0) {}

  ~EditDistanceTable() {
    if (costs_)
      delete costs_;
  }

  inline void update_row(const SequenceType &s, const SequenceType &t, 
                         unsigned j) {
    ValueType opt[3];

    for (int i=1; i<m_; ++i) {
      int s_pos=i-1, t_pos=j-1;

      opt[MATCH]  = cost(i-1, j-1) + ScoreType::match(s, t, s_pos, t_pos);
      opt[INSERT] = cost(  i, j-1) + ScoreType::insert(s, t, s_pos, t_pos);
      opt[DELETE] = cost(i-1,   j) + ScoreType::del(s, t, s_pos, t_pos);

      set_cost(i, j, MATCH, opt[MATCH]);

      for (int k=MATCH; k<=DELETE; ++k) {
        if (opt[k] < cost(i, j)) {
          set_cost(i, j, k, opt[k]);
        }
      }
    }
  }

  ValueType compute_editdistance() {
    costs_ = new std::vector<ValueType>(m_*n_, 0);
    for (int i=0; i<m_; ++i) {
      set_cost(i, 0, 0, i);
    }
    for (int j=0; j<n_; ++j) {
      set_cost(0, j, 0, j);
    }
    for (int j=1; j<n_; ++j) {
      update_row(s_, t_, j);
    }
    return cost(m_-1, n_-1);
  }

  inline void set_cost(unsigned i, unsigned j, unsigned k, ValueType cost) {
    (*costs_)[i + j*m_] = cost;
  }

  inline ValueType cost(unsigned i, unsigned j) const {
    return (*costs_)[i + j*m_];
  }

  const std::vector<ValueType>& costs() const { return *costs_; }

  void debug_print(std::ostream& os) const {
    int fwidth;
    os << " ";
    for (int i=0; i<m_; ++i) {
      fwidth = os.width(8);
      if (i == 0)
        os << "#";
      else
        os << s_[i-1];
      os.width(fwidth);
    }
    os << "\n";
    for (int j=0; j<n_; j++) {
      if (j == 0)
        os << "#";
      else
        os << t_[j-1];
      debug_print_cost_row(os, j);
      os << "\n";
    }
  }

  void debug_print_cost_row(std::ostream& os, int j) const {
    for (int i=0; i<m_; ++i) {
      int fwidth = os.width(8);
      os << cost(i,j);
      os.width(fwidth);
    }
  }

 protected:

  EditDistanceTable() {}

  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;
  std::vector<ValueType>* costs_;
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceTable< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////

template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceRow {
 public:
  EditDistanceRow(const SequenceType &s, const SequenceType &t) 
   : s_(s.size() > t.size() ? s : t), 
     t_(s.size() > t.size() ? t : s), 
     m_(s_.size()+1), 
     n_(t_.size()+1),
     costs_(0) {}

  ~EditDistanceRow() {
    if (costs_)
      delete [] costs_;
  }

  inline void update_row(const SequenceType &s, const SequenceType &t, 
                         unsigned j) {
    ValueType opt[3];
    set_cost(0, j, 0, j);

    for (int i=1; i<m_; ++i) {
      int s_pos=i-1, t_pos=j-1;

      opt[MATCH]  = cost(i-1, j-1) + ScoreType::match(s, t, s_pos, t_pos);
      opt[INSERT] = cost(  i, j-1) + ScoreType::insert(s, t, s_pos, t_pos);
      opt[DELETE] = cost(i-1,   j) + ScoreType::del(s, t, s_pos, t_pos);

      set_cost(i, j, MATCH, opt[MATCH]);

      for (int k=MATCH; k<=DELETE; ++k) {
        if (opt[k] < cost(i, j)) {
          set_cost(i, j, k, opt[k]);
        }
      }
    }
  }

  ValueType compute_editdistance() {
    costs_ = new ValueType[m_*2];
    for (int i=0; i<m_; ++i) {
      set_cost(i, 0, 0, i);
    }
    for (int j=1; j<n_; ++j) {
      update_row(s_, t_, j);
    }
    return cost(m_-1, n_-1);
  }

  inline void set_cost(unsigned i, unsigned j, unsigned k, ValueType cost) {
    //(*costs_)[i + (j % 2)*m_] = cost;
    costs_[i + (j % 2)*m_] = cost;
  }

  inline ValueType cost(unsigned i, unsigned j) const {
    //return (*costs_)[i + (j % 2)*m_];
    return costs_[i + (j % 2)*m_];
  }

 protected:
  EditDistanceRow() {}
  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;
  ValueType* costs_;
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceRow< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////

//#if 0
template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceRowIt {
 public:
  EditDistanceRowIt(size_t s_size, size_t t_size)
   : m_(s_size+1), 
     n_(t_size+1),
     costs_(0) {}

  ~EditDistanceRowIt() {
    if (costs_)
      delete [] costs_;
  }

  inline void update_row(typename SequenceType::const_iterator s_begin,
                         typename SequenceType::const_iterator t_begin,
                         unsigned j) {
    ValueType opt[3];
    set_cost(0, j, 0, j);

    for (int i=1; i<m_; ++i) {
      int s_pos=i-1, t_pos=j-1;

      uint8_t s_e = *(s_begin+s_pos);
      uint8_t t_e = *(t_begin+t_pos);
      opt[MATCH]  = cost(i-1, j-1) + ScoreType::match(s_e, t_e);
      opt[INSERT] = cost(  i, j-1) + ScoreType::insert(s_e, t_e);
      opt[DELETE] = cost(i-1,   j) + ScoreType::del(s_e, t_e);

      set_cost(i, j, MATCH, opt[MATCH]);

      for (int k=MATCH; k<=DELETE; ++k) {
        if (opt[k] < cost(i, j)) {
          set_cost(i, j, k, opt[k]);
        }
      }
    }
  }

  ValueType compute_editdistance(typename SequenceType::const_iterator &s_begin,
                                 typename SequenceType::const_iterator &t_begin) {

    costs_ = new ValueType[m_*2];
    for (int i=0; i<m_; ++i) {
      set_cost(i, 0, 0, i);
    }
    for (int j=1; j<n_; ++j) {
      update_row(s_begin, t_begin, j);
    }
    return cost(m_-1, n_-1);
  }

  inline void set_cost(unsigned i, unsigned j, unsigned k, ValueType cost) {
    //(*costs_)[i + (j % 2)*m_] = cost;
    costs_[i + (j % 2)*m_] = cost;
  }

  inline ValueType cost(unsigned i, unsigned j) const {
    //return (*costs_)[i + (j % 2)*m_];
    return costs_[i + (j % 2)*m_];
  }

 protected:
  EditDistanceRowIt() {}
  int m_, n_;
  ValueType* costs_;
};

//template<class ScoreType, class SequenceType, class ValueType>
//std::ostream& operator<<(std::ostream& os, 
//  const EditDistanceRowIt< ScoreType, SequenceType, ValueType > &edt) {
//  edt.debug_print(os);
//  return os;
//}
//#endif


////////////////////////////////////////////////////////////////////////////////

#define UDIM 100

template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceUkkonen {
 public:
  EditDistanceUkkonen(const SequenceType &s, const SequenceType &t) 
   : s_(s.size() > t.size() ? s : t), 
     t_(s.size() > t.size() ? t : s), 
     m_(s_.size()+1), 
     n_(t_.size()+1) {
    assert(m_ < UDIM);
  }

  ~EditDistanceUkkonen() {
  }

  inline ValueType U(int i, int j) const {
    return U_v[i+(UDIM/2)][j];
  }

  inline bool computed_U(int i, int j) const {
    return U_c[i+(UDIM/2)][j];
  }

  inline void set_U(int i, int j, ValueType v) {
    U_c[i+(UDIM/2)][j] = true;
    U_v[i+(UDIM/2)][j] = v;
  }

  ValueType Ukkonen(int ab, int d) {
    ValueType dist;
    if (std::abs(ab) > d) {
      return INT_MIN;
    }

    if (computed_U(ab,d)) {
      ValueType ret = U(ab, d);
      return ret;
    }

    dist = std::max(Ukkonen(ab+1, d-1), 
                    Ukkonen(ab,   d-1) + 1);
    dist = std::max(dist,
                    Ukkonen(ab-1, d-1) + 1);

    while (dist < (int)s_.size() && (dist-ab) < (int)t_.size() &&
           (ScoreType::match(s_, t_, dist, dist-ab) == 0)) {
      dist++;
    }

    set_U(ab, d, dist);
    return dist;
  }

  // As = s, Bs = t
  ValueType compute_editdistance() {
    //U_ = new ValueType[m_*m_];

    for (int i=0; i<UDIM; i++)
      for (int j=0; j<UDIM; j++)
        U_c[i][j] = false;       


    // U[0,0] = max i s.t. As[1...i] = Bs[1...i]
    int i = 1;
    while (i < ((int)t_.size()+1) && ScoreType::match(s_, t_, i-1, i-1) == 0)
      ++i;

    set_U(0, 0, i-1);

    ValueType edit_cost = 0;

    int s_size = s_.size();
    while (Ukkonen(s_.size()-t_.size(), edit_cost) < s_size) {
      edit_cost++;
    }

    return edit_cost;
  }

  void debug_print(std::ostream& os) const {
    for (int i=0; i<UDIM; ++i) {
      for (int j=0; j<UDIM; j++) {
        int fwidth = os.width(4);
        if (U_v[i][j] == INT_MIN)
          os << ".";
        else
          os << U_v[i][j];
        os.width(fwidth);
      }
      os << "\n";
    }
  }

 protected:
  EditDistanceUkkonen() {}

  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;
  ValueType U_v[UDIM][UDIM];
  ValueType U_c[UDIM][UDIM];
  //ValueType *U_v;
  //ValueType *U_c;
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceUkkonen< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////

// Non-recursive
template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceUKK {
 public:
  EditDistanceUKK(const SequenceType &s, const SequenceType &t) 
   : s_(s.size() > t.size() ? s : t), 
     t_(s.size() > t.size() ? t : s), 
     m_(s_.size()+1), 
     n_(t_.size()+1) {}

  ~EditDistanceUKK() {
  }

  inline ValueType U(int i, int j) const {
    if (std::abs(i) > j)
      return INT_MIN;
    return U_v[i+(UDIM/2)][j];
  }

  inline bool computed_U(int i, int j) const {
    if (std::abs(i) > j)
      return true;
    return U_c[i+(UDIM/2)][j];
  }

  inline void set_U(int i, int j, ValueType v) {
    U_c[i+(UDIM/2)][j] = true;
    U_v[i+(UDIM/2)][j] = v;
  }

  inline ValueType compute_U(int ab, int d) {

    ValueType d1, d2, d3, dist;
    if (computed_U(ab, d)) {
      dist = U(ab, d);
    } else {

      assert(computed_U(ab-1, d-1));
      assert(computed_U(ab, d-1));
      assert(computed_U(ab+1, d-1));

      d1 = U(ab+1, d-1);
      d2 = U(ab,   d-1) + 1;
      d3 = U(ab-1, d-1) + 1;
      dist = std::max(d1, std::max(d2, d3));

      while (dist < (int)s_.size() && (dist-ab) < (int)t_.size() &&
            (ScoreType::match(s_, t_, dist, dist-ab) == 0)) {
        dist++;
      }
    }
    return dist;
  }

  typedef std::stack<std::pair<int,int> > UStack;

  ValueType UKK(int ab, int d) {
    ValueType dist;
    UStack to_compute;

    for (int i=1; i<d; ++i) {
      bool all_clear = true;
      for (int j=-i; j<=i; ++j) {
        if (computed_U(ab+j, d-i) == false) {
          all_clear = false;
          to_compute.push(std::make_pair(ab+j, d-i));
        }
      }
      if (all_clear)
        break;
    }

    while (!to_compute.empty()) {
      int i = to_compute.top().first, j = to_compute.top().second;
      set_U(i, j, compute_U(i, j));
      to_compute.pop();
    }

    dist = compute_U(ab, d);

    set_U(ab, d, dist);
    return dist;
  }

  ValueType compute_editdistance() {

    for (int i=0; i<UDIM; i++)
      for (int j=0; j<UDIM; j++)
        U_v[i][j] = INT_MIN;
 
    for (int i=0; i<UDIM; i++)
      for (int j=0; j<UDIM; j++)
        U_c[i][j] = false;       

    // U[0,0] = max i s.t. As(s)[1...i] = Bs(t)[1...i]
    int i = 1;
    while (i < ((int)t_.size()+1) && ScoreType::match(s_, t_, i-1, i-1) == 0)
      ++i;

    set_U(0, 0, i-1);

    ValueType edit_cost = 0;

    int s_size = s_.size();
    while (UKK((int)s_.size()-(int)t_.size(), edit_cost) < s_size) {
      edit_cost++;
    }

    return edit_cost;
  }

  void debug_print(std::ostream& os) const {
    for (int i=0; i<UDIM; ++i) {
      for (int j=0; j<UDIM; j++) {
        int fwidth = os.width(4);
        if (U_v[i][j] == INT_MIN)
          os << ".";
        else
          os << U_v[i][j];
        os.width(fwidth);
      }
      os << "\n";
    }
  }

 protected:
  EditDistanceUKK() {}
  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;
  ValueType U_v[UDIM][UDIM];
  ValueType U_c[UDIM][UDIM];
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceUKK< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////

template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceDynamicUKK {
 public:
  EditDistanceDynamicUKK(const SequenceType &s, const SequenceType &t) 
   : s_(s.size() > t.size() ? s : t), 
     t_(s.size() > t.size() ? t : s), 
     m_(s_.size()+1), 
     n_(t_.size()+1) {}

  ~EditDistanceDynamicUKK() {
    for (int i=0; i< max_edit_distance_; ++i)
      free(U_[i]);
    free(U_col_);
    free(U_);
  }

  inline ValueType U(int i, int j) const {
    if (std::abs(i) > j)
      return INT_MIN;
    assert(j < max_edit_distance_ && get_row(i) < U_col_[j]);
    return U_[j][get_row(i)];
  }

  inline bool computed_U(int i, int j) const {
    if (std::abs(i) > j)
      return true;
    if (j >= max_edit_distance_ || get_row(i) >= U_col_[j])
      return false;
    return U_[j][get_row(i)] != -1;
  }

  inline void set_U(int i, int j, ValueType v) {
    if (std::abs(i) > j) {
      assert(v = INT_MIN);
      return;
    }
    if (j >= max_edit_distance_ || get_row(i) >= U_col_[j])
      alloc_column(i, j);

    U_[j][get_row(i)] = v;
  }

  inline unsigned get_row(int i) const {
    if (i < 0)
      return (i*-2)-1;
    return i*2;
  }

  inline ValueType compute_U(int ab, int d) {

    ValueType d1, d2, d3, dist;

    if (computed_U(ab, d)) {
      dist = U(ab, d);
      if (ab == 0 && d == 0) {
        while (dist < (int)s_.size() && (dist-ab) < (int)t_.size() &&
              (ScoreType::match(s_, t_, dist, dist-ab) == 0)) {
          dist++;
        }
      }
    } else {

      assert(computed_U(ab-1, d-1));
      assert(computed_U(ab, d-1));
      assert(computed_U(ab+1, d-1));

      d1 = U(ab+1, d-1);
      d2 = U(ab,   d-1) + 1;
      d3 = U(ab-1, d-1) + 1;
      dist = std::max(d1, std::max(d2, d3));

      while (dist < (int)s_.size() && (dist-ab) < (int)t_.size() &&
            (ScoreType::match(s_, t_, dist, dist-ab) == 0)) {
        dist++;
      }
    }
    return dist;
  }

  typedef std::stack<std::pair<int,int> > UStack;

  ValueType UKK(int ab, int d) {
    ValueType dist;
    UStack to_compute;

    for (int i=1; i<d; ++i) {
      bool all_clear = true;
      for (int j=-i; j<=i; ++j) {
        if (computed_U(ab+j, d-i) == false) {
          all_clear = false;
          to_compute.push(std::make_pair(ab+j, d-i));
        }
      }
      if (all_clear)
        break;
    }

    while (!to_compute.empty()) {
      int i = to_compute.top().first, j = to_compute.top().second;
      set_U(i, j, compute_U(i, j));
      to_compute.pop();
    }

    dist = compute_U(ab, d);

    set_U(ab, d, dist);
    return dist;
  }

  void alloc_column(int i, int j) {
    int col_size = 0;
    if (j == 0) {
      col_size = 1;
    } else {
      assert(U_col_[j-1] > 0);
      col_size = std::max(U_col_[j-1], get_row(i)) + 1;
    }

    if (j >= max_edit_distance_) {
      U_col_[j] = 0;
      U_[j] = (ValueType*) malloc(col_size * sizeof(ValueType));
      assert(U_[j]);
      max_edit_distance_++;
    } else {
      U_[j] = (ValueType*) realloc(U_[j], col_size * sizeof(ValueType));
      assert(U_[j]);
    }

    // Initialize values
    for (ValueType k=U_col_[j]; k<col_size; ++k) {
      U_[j][k] = -1;
    }

    U_col_[j] = col_size;
  }

  ValueType compute_editdistance() {

    max_edit_distance_ = 0;
    U_col_ = (unsigned*) malloc((s_.size()+1) * sizeof(unsigned));
    U_ = (ValueType**) malloc((s_.size()+1) * sizeof(ValueType*));

    alloc_column(0, 0);

    // U[0,0] = max i s.t. As(s)[1...i] = Bs(t)[1...i]
    int i = 1;
    while (i < ((int)t_.size()+1) && ScoreType::match(s_, t_, i-1, i-1) == 0)
      ++i;

    set_U(0, 0, i-1);

    ValueType edit_cost = 0;

    int s_size = s_.size();
    while (UKK(s_.size()-t_.size(), edit_cost) < s_size) {
      edit_cost++;
    }

    return edit_cost;
  }

  void debug_print(std::ostream& os) const {
    unsigned max_col = 0;

    for (int j=0; j<max_edit_distance_; j++) 
      max_col = std::max(max_col, U_col_[j]/2);

    for (int j=0; j<max_edit_distance_; j++) {

      for (int i=0; i < max_col - U_col_[j]/2; ++i) {
        int fwidth = os.width(4);
        os << ".";
        os.width(fwidth);
      }

      int start=-(int)(U_col_[j]/2), end = (U_col_[j])/2;
      if (start == end) end++;
      for (int i=start; i < end; ++i) {
        int fwidth = os.width(4);
        if (U_[j][get_row(i)] == -1)
          os << ".";
        else
          os << U_[j][get_row(i)];
        os.width(fwidth);
      }
      for (int i=0; i < max_col - U_col_[j]/2; ++i) {
        int fwidth = os.width(4);
        os << ".";
        os.width(fwidth);
      }

      os << "\n";
    }
  }

 protected:
  EditDistanceDynamicUKK() {}
  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;

  ValueType** U_;
  unsigned* U_col_;
  ValueType max_edit_distance_;
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceDynamicUKK< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////

template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceStaticUKK {
 public:
  EditDistanceStaticUKK(const SequenceType &s, const SequenceType &t) 
   : s_(s.size() > t.size() ? s : t), 
     t_(s.size() > t.size() ? t : s), 
     m_(s_.size()+1), 
     n_(t_.size()+1) {}

  ~EditDistanceStaticUKK() {
  }

  inline ValueType U(int i, int j) {
    if (std::abs(i) > j)
      return INT_MIN;
    return U_[std::make_pair(i,j)];
  }

  inline bool computed_U(int i, int j) const {
    if (std::abs(i) > j)
      return true;
    return U_.count(std::make_pair(i,j));
  }

  inline void set_U(int i, int j, ValueType v) {
    U_[std::make_pair(i,j)] = v;
  }

  inline ValueType compute_U(int ab, int d) {

    ValueType d1, d2, d3, dist;
    if (computed_U(ab, d)) {
      dist = U(ab, d);
    } else {

      assert(computed_U(ab-1, d-1));
      assert(computed_U(ab, d-1));
      assert(computed_U(ab+1, d-1));

      d1 = U(ab+1, d-1);
      d2 = U(ab,   d-1) + 1;
      d3 = U(ab-1, d-1) + 1;
      dist = std::max(d1, std::max(d2, d3));

      while (dist < s_.size() && (dist-ab) < t_.size() &&
            (ScoreType::match(s_, t_, dist, dist-ab) == 0)) {
        dist++;
      }
    }
    return dist;
  }

  typedef std::stack<std::pair<int,int> > UStack;

  ValueType UKK(int ab, int d) {
    ValueType dist;
    UStack to_compute;

    for (int i=1; i<d; ++i) {
      bool all_clear = true;
      for (int j=-i; j<=i; ++j) {
        if (computed_U(ab+j, d-i) == false) {
          all_clear = false;
          to_compute.push(std::make_pair(ab+j, d-i));
        }
      }
      if (all_clear)
        break;
    }

    while (!to_compute.empty()) {
      int i = to_compute.top().first, j = to_compute.top().second;
      set_U(i, j, compute_U(i, j));
      to_compute.pop();
    }

    dist = compute_U(ab, d);

    set_U(ab, d, dist);
    return dist;
  }

  ValueType compute_editdistance() {
    int i = 1;
    while (i < ((int)t_.size()+1) && ScoreType::match(s_, t_, i-1, i-1) == 0)
      ++i;

    set_U(0, 0, i-1);

    ValueType edit_cost = 0;

    int s_size = s_.size();
    while (UKK(s_.size()-t_.size(), edit_cost) < s_size) {
      edit_cost++;
    }

    return edit_cost;
  }

  void debug_print(std::ostream& os) const {
    os << "debug_print not supported\n";
  }

 protected:
  EditDistanceStaticUKK() {}
  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;

  std::map<std::pair<int,int>, ValueType> U_;
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceStaticUKK< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////

#define ROW_INDEX(x) ((x) < 0 ? (((x)*-2)-1) : ((x)*2))
#define NEG_INF INT_MIN

template<class ScoreType, class SequenceType, class ValueType>
class EditDistanceFullUKK {
 public:
  EditDistanceFullUKK(const SequenceType &s, const SequenceType &t) 
   : s_(s.size() > t.size() ? s : t), 
     t_(s.size() > t.size() ? t : s), 
     m_(s_.size()+1), 
     n_(t_.size()+1), U_(0) {}

  ~EditDistanceFullUKK() {
    if (U_)
      delete [] U_;
  }

  inline ValueType U(int i, int j) {
    if (std::abs(i) > j)
      return NEG_INF;
    return U_[ROW_INDEX(i) + ((j % 2)*(m_*2))];
  }

  inline void set_U(int i, int j, ValueType v) {
    U_[ROW_INDEX(i) + ((j % 2)*(m_*2))] = v;
  }

  inline unsigned get_row(int i) const {
    if (i < 0)
      return (i*-2)-1;
    return i*2;
  }

  inline ValueType compute_U(int ab, int d) {

    ValueType d1, d2, d3, dist;

    if (std::abs(ab) > d) {
      return NEG_INF;
    } else {

      if (ab == 0 && d == 0) {
        dist = U(ab, d);
      } else {
        d1 = U(ab+1, d-1);
        d2 = U(ab,   d-1) + 1;
        d3 = U(ab-1, d-1) + 1;
        dist = std::max(d1, std::max(d2, d3));
      }

      while (dist < (int)s_.size() && (dist-ab) < (int)t_.size() &&
            (ScoreType::match(s_, t_, dist, dist-ab) == 0)) {
        dist++;
      }
    }
    return dist;
  }

  typedef std::stack<std::pair<int,int> > UStack;

  ValueType UKK(int ab, int d) {
    ValueType dist;

    int i = 0;
    while (std::abs(i) <= d) {
      dist = compute_U(i, d);
      set_U(i, d, dist);
      i--;
    }
    i = 1;
    while (std::abs(i) <= d) {
      dist = compute_U(i, d);
      set_U(i, d, dist);
      i++;
    }

    if (std::abs(ab) > d)
      return NEG_INF;
    return U(ab, d);
  }

  ValueType compute_editdistance() {
 
    U_ = new ValueType[m_*4];

    int i = 1;
    while (i < ((int)t_.size()+1) && ScoreType::match(s_, t_, i-1, i-1) == 0)
      ++i;

    set_U(0, 0, i-1);

    ValueType edit_cost = 0;

    int s_size = s_.size();
    while (UKK(s_.size()-t_.size(), edit_cost) < s_size) {
      edit_cost++;
    }

    return edit_cost;
  }

  void debug_print(std::ostream& os) const {
    os << "debug_print not supported\n";
  }

 protected:
  EditDistanceFullUKK() {}
  const SequenceType &s_;
  const SequenceType &t_;
  int m_, n_;
  ValueType* U_;
};

template<class ScoreType, class SequenceType, class ValueType>
std::ostream& operator<<(std::ostream& os, 
  const EditDistanceFullUKK< ScoreType, SequenceType, ValueType > &edt) {
  edt.debug_print(os);
  return os;
}

////////////////////////////////////////////////////////////////////////////////

} // end namespace cliver

#endif // CLIVER_EDITDISTANCH_H
